###############################################################################
# R Script for Extracting Basin Attributes for Clustering Hydrometric Gauges
#
# Author: Scott Pokorny
# Date: 2025-04-21
#
# This script performs the following major tasks:
#  1. Identifies hydrometric gauge stations and their associated basin polygons.
#  2. Filters stations based on HYDAT flow data availability and quality.
#  3. Extracts station properties (ID, latitude, longitude) and writes to CSV.
#  4. Processes land cover raster (NALCMS) to compute percentage coverage per basin.
#  5. Processes MERIT-HYDRO DEM to compute elevation statistics and average slope.
#  6. Extracts daily weather timeseries (precipitation, tasmin, tasmax) from HydroGFD.
#     a. Merges and derives mean temperature and daily range.
#     b. Writes per‐station CSV of full timeseries.
#  7. Computes summary temperature statistics for each station (annual means, percentiles).
#  8. Computes standardized temperature event metrics and fits Gaussian seasonal cycle.
#  9. Computes flow statistics: L‐moments, AR(1) coefficient, seasonal signal fitting.
# 10. Computes water temperature Gaussian fit parameters.
# 11. Computes basin lake‐area percentage using LakeATLAS polygons.
# 12. Merges all attribute tables into one master CSV.
# 13. Fits Random Forest models to predict water‐temperature parameters.
# 14. Performs unsupervised RF + PAM clustering with Monte Carlo sampling of predictors.
#
# The purpose of this script is to step through the clustering process presented in
# the accompanying publication
# Pokorny S., Ali G., Stadnyk T.A., (submitted). Unlocking Canada's Rivers: A Novel
# Classification of Thermal Regimes Using Advanced Clustering Techniques. Manuscript
# submitted to the CWRJ.
###############################################################################

#--------------------------------------
# 0. Load Required Libraries
#--------------------------------------
# sf          : vector spatial data (shapefiles)
# raster      : raster data handling
# dplyr       : data manipulation
# tidyhydat   : Canadian HYDAT flow data access
# ncdf4       : NetCDF file interface
# lubridate   : date handling
# zoo         : rolling window functions
# exactextractr: efficient raster extraction
# minpack.lm  : nonlinear least squares fitting (nlsLM)
# lmom        : L‐moment calculations
# stats       : AR model, regression
# randomForest: Random Forest modeling
# cluster     : clustering (pam)
library(sf)
library(raster)
library(dplyr)
library(tidyhydat)
library(ncdf4)
library(lubridate)
library(zoo)
library(exactextractr)

library(minpack.lm)    
library(lmom)          
library(stats)         
library(randomForest)  
library(cluster)


###############################################################################
# 1. Identify Basin Files and Station Shapefiles
###############################################################################

# Base directory containing regional subfolders "01" to "11". Note, this assumes
# that the WSC basins were downloaded and extracted to a folder
basin_dir <- "C:/water_temp/wsc/"

# Generate folder names "01", "02", ..., "11"
folder_list <- sprintf("%02d", 1:11)

# Initialize list to hold station metadata
station_info <- list()

# Loop over each folder (region)
for (folder in folder_list) {
  folder_path <- file.path(basin_dir, folder)
  
  # List immediate subdirectories (each corresponds to a station)
  station_dirs <- list.dirs(path = folder_path, full.names = TRUE, recursive = FALSE)
  
  for (station_path in station_dirs) {
    # Derive station ID from folder name
    station_id <- basename(station_path)
    
    # Construct expected shapefile paths
    basin_shp <- file.path(station_path, paste0(station_id, "_DrainageBasin_BassinDeDrainage.shp"))
    station_shp <- file.path(station_path, paste0(station_id, "_Station.shp"))
    
    # Only keep stations where both shapefiles exist
    if (file.exists(basin_shp) && file.exists(station_shp)) {
      station_info[[station_id]] <- list(
        station_id = station_id,
        basin_shp = basin_shp,
        station_shp = station_shp
      )
    }
  }
}

# Report total stations discovered
cat("Number of stations found:", length(station_info), "\n")


###############################################################################
# 1.1 Filter Stations Based on HYDAT Flow Data Criteria
###############################################################################

# Initialize list for stations that meet data criteria
filtered_station_info <- list()

for (station in station_info) {
  
  # a) Check if any flow data exist for this station
  flow_info <- hy_stn_data_coll(station$station_id)
  if (!any(flow_info$DATA_TYPE == "Flow")) {
    cat("Skipping station", station$station_id, "due to no flow data.\n")
    next
  }
  
  # b) Attempt to fetch daily flows (1994-2016); skip on error
  skip_to_next <- FALSE
  data <- tryCatch({
    hy_daily_flows(station$station_id)
  }, error = function(e) {
    cat("Error fetching daily flows for station", station$station_id, "\n")
    skip_to_next <<- TRUE
    NULL
  })
  
  if (skip_to_next || is.null(data)) {
    next
  }
  
  # c) Ensure coverage includes both 1994 and 2016
  if (!any(year(data$Date) >= 1994)) {
    cat("Skipping station", station$station_id, "due to insufficient early data.\n")
    next
  }
  if (!any(year(data$Date) <= 2016)) {
    cat("Skipping station", station$station_id, "due to insufficient recent data.\n")
    next
  }
  
  # d) Subset to 1994-2016 period
  data_filtered <- data[year(data$Date) >= 1994 & year(data$Date) <= 2016, ]
  
  # e) Require at least ~3 years of daily data (~365*3 non-NA days)
  if (sum(!is.na(data_filtered$Value)) <= 365 * 3) {
    cat("Skipping station", station$station_id, "due to insufficient data points.\n")
    next
  }
  
  # f) Exclude if mean flow is zero (indicates no valid data)
  if (mean(data_filtered$Value, na.rm=TRUE) == 0) {
    cat("Skipping station", station$station_id, "due to insufficient data points.\n")
    next
  }
  
  # Passes all filters: attach filtered data and keep station
  station$data <- data_filtered
  filtered_station_info[[station$station_id]] <- station
}

# Update station_info and report
cat("Number of stations after filtering:", length(filtered_station_info), "\n")
station_info <- filtered_station_info


###############################################################################
# 2. Extract Station Coordinates & Write station_properties.csv
###############################################################################

# Prepare empty dataframe
station_properties <- data.frame()

for (station in names(station_info)) {
  cat("Processing data for station:", station, "\n")
  
  # Read point shapefile for gauge location
  gauge_shp_path <- station_info[[station]]$station_shp
  gauge_sf <- st_read(gauge_shp_path, quiet = TRUE)
  coords <- st_coordinates(gauge_sf) # Extract X/Y coords
  lon <- coords[1, "X"]
  lat <- coords[1, "Y"]
  
  row <- data.frame(
    station_id     = station,
    lon  = lon,
    lat  = lat,
    stringsAsFactors = FALSE
  )
  
  # Append to dataframe
  station_properties <- rbind(station_properties, row)
}

# Write out station properties
write.csv(station_properties,
          "station_properties.csv",
          row.names = FALSE)


###############################################################################
# 3. Landclass Raster Processing (NALCMS)
###############################################################################

# Load the 2015 North American Land Cover raster (30m resolution)
landclass_path <- "C:/water_temp/NA_NALCMS_landcover_2015v2_30m.tif"
landclass_raster <- raster(landclass_path)

# Initialize storage for each station's landclass percentages
landclass_summary <- list()

# Loop over stations to extract land cover distribution
for (station in station_info) {
  print(paste0("grabbing land classes for ", station$station_id))
  
  # Read basin polygon as sf
  basin_poly <- st_read(station$basin_shp, quiet = TRUE)

  # Ensure projection matches raster CRS
  if (st_crs(basin_poly) != crs(landclass_raster)) {
    basin_poly <- st_transform(basin_poly, crs(landclass_raster))
  }

  # Convert to Spatial object if needed for raster functions
  data <- tryCatch({
    basin_sp <- as(basin_poly, "Spatial")
  }, error = function(e) {
    cat("This station probably has a z dimension: ", station$station_id, "\n")
    basin_sp <- basin_poly # work around for z polygons
  })

  # Crop & mask to basin extent to limit memory usage
  lc_crop <- crop(landclass_raster, extent(basin_sp))
  lc_mask <- mask(lc_crop, basin_sp)

  # Extract values, drop NA
  lc_values <- getValues(lc_mask)
  lc_values <- lc_values[!is.na(lc_values)]

  # Clean up
  rm(lc_mask)
  gc()

  # Compute frequency table → percentages
  if (length(lc_values) > 0) {
    freq_table <- table(lc_values)
    percent <- (freq_table / sum(freq_table)) * 100
    landclass_summary[[station$station_id]] <- percent
  } else {
    landclass_summary[[station$station_id]] <- NA
  }
}

# Build dataframe of landclass percentages 1–19
landcover_df <- data.frame(station_id = names(landclass_summary),
                           stringsAsFactors = FALSE)

# Loop over land classes 1 to 19
for (lc in 1:19) {
  # Create a column name for this land class
  lc_col <- paste0("land_class_", lc)

  # For each station, extract the percentage for the given land class or 0 if missing
  landcover_df[[lc_col]] <- sapply(landclass_summary, function(x) {
    # If x is NA or empty, return 0
    if (is.null(x) || all(is.na(x))) {
      return(0)
    }
    # x is a named numeric vector; check if the land class exists
    if (as.character(lc) %in% names(x)) {
      return(as.numeric(x[as.character(lc)]))
    } else {
      return(0)
    }
  })
}

# Write out landcover attributes
write.csv(landcover_df,
          "canadian_lc_attributes.csv",
          row.names = FALSE)

###############################################################################
# 4. Elevation Data Processing (MERIT-HYDRO DEM)
###############################################################################

# Load the MERIT-HYDRO DEM raster (assumes a single mosaic dem for Canada)
dem_path <- "C:/water_temp/merit_north_america.tif"
dem_raster <- raster(dem_path)

# Initialize storage for elevation summaries
dem_summary <- list()

# Loop over each station to extract elevation statistics and slope
for (station in station_info) {
  print(paste0("grabbing elevation data for ", station$station_id))

  # Read basin polygon
  basin_poly <- st_read(station$basin_shp, quiet = TRUE)
  if (st_crs(basin_poly) != crs(dem_raster)) {
    basin_poly <- st_transform(basin_poly, crs(dem_raster))
  }

  # Convert to Spatial object
  data <- tryCatch({
    basin_sp <- as(basin_poly, "Spatial")
  }, error = function(e) {
    cat("This station probably has a z dimension: ", station$station_id, "\n")
    basin_sp <- basin_poly # work around for z polygons
  })

  # Crop & mask DEM
  dem_crop <- crop(dem_raster, extent(basin_sp))
  dem_mask <- mask(dem_crop, basin_sp)

  # Extract elevations, drop NA
  dem_values <- getValues(dem_mask)
  dem_values <- dem_values[!is.na(dem_values)]

  if (length(dem_values) > 0) {
    # Compute summary stats
    basin_area <- basin_poly$Area_km2
    dem_min    <- min(dem_values)
    dem_mean   <- mean(dem_values)
    dem_max    <- max(dem_values)
    dem_median <- median(dem_values)
    dem_range  <- dem_max - dem_min
    dem_sd     <- sd(dem_values)

    # Compute slope (deg) using 8‐neighbor terrain
    slope_raster <- terrain(dem_mask, opt = "slope", unit = "degrees", neighbors = 8)
    slope_values <- getValues(slope_raster)
    slope_values <- slope_values[!is.na(slope_values)]
    avg_slope    <- ifelse(length(slope_values) > 0, mean(slope_values), NA)

    # Store computed metrics in a list for the station
    dem_summary[[station$station_id]] <- list(
      area      = basin_area,
      min       = dem_min,
      mean      = dem_mean,
      max       = dem_max,
      median    = dem_median,
      range     = dem_range,
      sd        = dem_sd,
      avg_slope = avg_slope
    )
  } else {
    dem_summary[[station$station_id]] <- NA
  }
}

# Assemble into dataframe
dem_stats_df <- data.frame()
for (station_id in names(dem_summary)) {
  # Convert the list of stats into a data frame row
  row <- data.frame(
    station_id = station_id,
    basin_area = dem_summary[[station_id]]$area,
    dem_min    = dem_summary[[station_id]]$min,
    dem_mean   = dem_summary[[station_id]]$mean,
    dem_max    = dem_summary[[station_id]]$max,
    dem_median = dem_summary[[station_id]]$median,
    dem_range  = dem_summary[[station_id]]$range,
    dem_sd     = dem_summary[[station_id]]$sd,
    dem_avg_slope = dem_summary[[station_id]]$avg_slope
  )

  dem_stats_df <- rbind(dem_stats_df, row)
}

# Write out DEM attributes
write.csv(dem_stats_df,
          "canadian_dem_attributes.csv",
          row.names = FALSE)


###############################################################################
# 5. HydroGFD Gridded Weather Data Extraction Function
###############################################################################

# Function to extract daily basin & gauge values for tasmin and tasmax
extract_weather_timeseries <- function(station, var, start_year, end_year, data_dir) {
  
  # Initialize empty DF
  weather_df <- data.frame(date        = as.Date(character()),
                           basin_value = numeric(),
                           gauge_value = numeric(),
                           stringsAsFactors = FALSE)
  
  # Read basin polygon & gauge point
  basin_poly <- st_read(station$basin_shp, quiet    = TRUE)
  gauge_point <- st_read(station$station_shp, quiet = TRUE)
  
  basin_poly <- st_make_valid(basin_poly)
  
  # Loop yearly & monthly
  month_str <- sprintf("%02d", 1)
  file_path <- file.path(data_dir, as.character(start_year),
                         paste0("hydrogfd3.0_", var, "_", start_year, month_str, ".nc"))

  # Load as raster brick
  nc_brick <- brick(file_path)
  
  # Reproject station data to match brick CRS
  if (st_crs(basin_poly) != crs(nc_brick)) {
    basin_poly <- st_transform(basin_poly, crs(nc_brick))
  }
  if (st_crs(gauge_point)!= crs(nc_brick)) {
    gauge_point <- st_transform(gauge_point, crs(nc_brick))
  }
  
  # Spatial objects
  data <- tryCatch({
    basin_sp <- as(basin_poly,  "Spatial")
    gauge_sp <- as(gauge_point, "Spatial")
  }, error = function(e) {
    cat("This station probably has a z dimension: ", station$station_id, "\n")
    basin_sp <- basin_poly
    gauge_sp <- gauge_point # work around for z polygons
  })
  
  # Loop through each year and month
  for (year in start_year:end_year) {
    for (month in 1:12) {
      
      # Construct filename: hydrogfd3.0_{var}_{year}{month}.nc
      month_str <- sprintf("%02d", month)
      file_path <- file.path(data_dir, as.character(year),
                             paste0("hydrogfd3.0_", var, "_", year, month_str, ".nc"))
      
      # Skip if the file does not exist
      if (!file.exists(file_path)) next
      
      # Load as raster brick
      nc_brick <- brick(file_path)
      
      # Determine number of days (layers)
      n_days <- nlayers(nc_brick)
      dates <- seq(from = as.Date(paste(year, month_str, "01", sep = "-")),
                   by = "day", length.out = n_days)
      
      nc_brick_crop <- crop(nc_brick, extent(basin_sp))
      
      # Extract daily basin values using exactextractr
      basin_vals <- t(exactextractr::exact_extract(nc_brick_crop, basin_sp, 'mean'))
      
      # Extract daily gauge values (point extraction)
      gauge_vals <- extract(nc_brick, gauge_sp)
      gauge_vals <- as.numeric(gauge_vals[1, ])
      
      # Combine the extracted values with the dates
      month_df <- data.frame(date = dates,
                             basin_value = basin_vals,
                             gauge_value = gauge_vals,
                             stringsAsFactors = FALSE)
      weather_df <- rbind(weather_df, month_df)

    }
  }
  
  return(weather_df)
}

# Define HydroGFD directory & period
hydrogfd_dir <- "C:/water_temp/hydrogfd"
start_year   <- 1994
end_year     <- 2016

###############################################################################
# 6. Extract & Save Full Daily Weather Timeseries per Station
###############################################################################

for (station in station_info) {
  cat("Processing weather data for station:", station$station_id, "\n")

  # Minimum temperature (convert Kelvin→°C)
  tasmin_ts <- extract_weather_timeseries(station, "tasmin", start_year, end_year, hydrogfd_dir)
  tasmin_ts[,c(2,3)] <- round(tasmin_ts[,c(2,3)] - 273.15, 2)
  names(tasmin_ts)[2:3] <- c("basin_tasmin", "gauge_tasmin")

  # Maximum temperature (convert Kelvin→°C)
  tasmax_ts <- extract_weather_timeseries(station, "tasmax", start_year, end_year, hydrogfd_dir)
  tasmax_ts[,c(2,3)] <- round(tasmax_ts[,c(2,3)] - 273.15, 2)
  names(tasmax_ts)[2:3] <- c("basin_tasmax", "gauge_tasmax")

  # Merge and derive
  weather_ts <- merge(tasmax_ts, tasmin_ts, by = "date")
  weather_ts$basin_tmean      <- (weather_ts$basin_tasmin + weather_ts$basin_tasmax) / 2
  weather_ts$gauge_tmean      <- (weather_ts$gauge_tasmin + weather_ts$gauge_tasmax) / 2
  weather_ts$basin_temp_range <- weather_ts$basin_tasmax - weather_ts$basin_tasmin
  weather_ts$gauge_temp_range <- weather_ts$gauge_tasmax - weather_ts$gauge_tasmin

  # Save CSV per station
  write.csv(weather_ts,
            paste0("./hydrogfd_wsc/",
                   station$station_id,
                   "_hydrogfd.csv"),
            row.names = FALSE)
}

###############################################################################
# 7. Compute Summary Temperature Statistics Function
###############################################################################

compute_temperature_stats <- function(weather_ts, location = c("basin", "gauge")) {
  location <- match.arg(location)
  
  # Select appropriate column names based on location
  tmin_col  <- paste0(location, "_tasmin")
  tmean_col <- paste0(location, "_tmean")
  tmax_col  <- paste0(location, "_tasmax")
  range_col <- paste0(location, "_temp_range")
  
  # Add year & day-of-year
  weather_ts <- weather_ts %>%
    mutate(year = year(date),
           doy = yday(date))
  
  # Annual stats: mean, sd, cv, CDD, avg range
  annual_stats <- weather_ts %>%
    group_by(year) %>%
    summarize(
      mean_tmin = mean(get(tmin_col), na.rm = TRUE),
      sd_tmin   = sd(get(tmin_col), na.rm = TRUE),
      cv_tmin   = sd_tmin / mean_tmin,
      
      mean_tmean = mean(get(tmean_col), na.rm = TRUE),
      sd_tmean   = sd(get(tmean_col), na.rm = TRUE),
      cv_tmean   = sd_tmean / mean_tmean,
      
      mean_tmax = mean(get(tmax_col), na.rm = TRUE),
      sd_tmax   = sd(get(tmax_col), na.rm = TRUE),
      cv_tmax   = sd_tmax / mean_tmax,
      
      # Cumulative degree days for mean temperature (only positive values)
      cdd = sum(ifelse(get(tmean_col) > 0, get(tmean_col), 0), na.rm = TRUE),
      
      # Average daily temperature range
      avg_range = mean(get(range_col), na.rm = TRUE)
    )
  
  # Aggregate annual → overall averages
  avg_annual <- annual_stats %>%
    summarize(
      avg_mean_tmin = mean(mean_tmin, na.rm = TRUE),
      avg_sd_tmin   = mean(sd_tmin, na.rm = TRUE),
      avg_cv_tmin   = mean(cv_tmin, na.rm = TRUE),
      
      avg_mean_tmean = mean(mean_tmean, na.rm = TRUE),
      avg_sd_tmean   = mean(sd_tmean, na.rm = TRUE),
      avg_cv_tmean   = mean(cv_tmean, na.rm = TRUE),
      
      avg_mean_tmax = mean(mean_tmax, na.rm = TRUE),
      avg_sd_tmax   = mean(sd_tmax, na.rm = TRUE),
      avg_cv_tmax   = mean(cv_tmax, na.rm = TRUE),
      
      avg_cdd = mean(cdd, na.rm = TRUE),
      avg_daily_range = mean(avg_range, na.rm = TRUE)
    )
  
  # Percentile DOY for mean temperature
  percentile_dates <- weather_ts %>%
    group_by(year) %>%
    do({
      df <- .
      n <- nrow(df)
      # Order the data by daily mean temperature
      ordered <- df[order(df[[tmean_col]]), ]
      # Determine the index corresponding to each percentile.
      p5_index   <- max(1, round(0.05 * n))
      p25_index  <- max(1, round(0.25 * n))
      p50_index  <- max(1, round(0.50 * n))
      p75_index  <- max(1, round(0.75 * n))
      data.frame(
        p5_doy  = ordered$doy[p5_index],
        p25_doy = ordered$doy[p25_index],
        p50_doy = ordered$doy[p50_index],
        p75_doy = ordered$doy[p75_index]
      )
    }) %>%
    ungroup() %>%
    summarize(
      avg_p5_doy  = mean(p5_doy, na.rm = TRUE),
      avg_p25_doy = mean(p25_doy, na.rm = TRUE),
      avg_p50_doy = mean(p50_doy, na.rm = TRUE),
      avg_p75_doy = mean(p75_doy, na.rm = TRUE)
    )
  
  # Annual day-of-year for the minimum temperature (from tasmin series)
  min_temp_dates <- weather_ts %>%
    group_by(year) %>%
    summarize(min_temp_doy = doy[which.min(get(tmin_col))]) %>%
    ungroup() %>%
    summarize(avg_min_temp_doy = mean(min_temp_doy, na.rm = TRUE))
  
  # Annual coldest 7-day period from the tasmin series
  coldest_7day_dates <- weather_ts %>%
    group_by(year) %>%
    do({
      df <- .
      if(nrow(df) < 7) return(data.frame(cold7_doy = NA))
      # Rolling mean over 7 days (centered)
      roll_mean <- rollapply(df[[tmin_col]], width = 7, FUN = mean, align = "center", fill = NA)
      cold7_index <- which.min(roll_mean)
      data.frame(cold7_doy = df$doy[cold7_index])
    }) %>%
    ungroup() %>%
    summarize(avg_cold7_doy = mean(cold7_doy, na.rm = TRUE))
  
  # Annual hottest day from the tasmax series
  hottest_day_dates <- weather_ts %>%
    group_by(year) %>%
    summarize(hot_day_doy = doy[which.max(get(tmax_col))]) %>%
    ungroup() %>%
    summarize(avg_hot_day_doy = mean(hot_day_doy, na.rm = TRUE))
  
  # Annual hottest 7-day period from the tasmax series
  hottest_7day_dates <- weather_ts %>%
    group_by(year) %>%
    do({
      df <- .
      if(nrow(df) < 7) return(data.frame(hot7_doy = NA))
      roll_mean <- rollapply(df[[tmax_col]], width = 7, FUN = mean, align = "center", fill = NA)
      hot7_index <- which.max(roll_mean)
      data.frame(hot7_doy = df$doy[hot7_index])
    }) %>%
    ungroup() %>%
    summarize(avg_hot7_doy = mean(hot7_doy, na.rm = TRUE))
  
  # Combine all computed statistics into one list
  stats <- list(
    avg_annual_temp_stats = avg_annual,
    percentile_dates    = percentile_dates,
    min_temp_date       = min_temp_dates,
    coldest_7day_date   = coldest_7day_dates,
    hottest_day_date    = hottest_day_dates,
    hottest_7day_date   = hottest_7day_dates
  )
  
  return(stats)
}

###############################################################################
# 8. Loop Stations to Compute & Save Summary Temperature Stats
###############################################################################

temp_stats_df <- data.frame()

for (station in station_info) {
  cat("Computing temperature stats for station:", station$station_id, "\n")
  
  ts_data <- read.csv(paste0("./hydrogfd_wsc/",
                              station$station_id,
                              "_hydrogfd.csv"))
  basin_stats <- compute_temperature_stats(ts_data, location = "basin")
  gauge_stats <- compute_temperature_stats(ts_data, location = "gauge")
    
  # Flatten into one row
  row <- data.frame(
    id = station$station_id,
    bsn_avg_mean_tmin = basin_stats$avg_annual_temp_stats$avg_mean_tmin,
    bsn_avg_sd_tmin   = basin_stats$avg_annual_temp_stats$avg_sd_tmin,
    bsn_avg_cv_tmin   = basin_stats$avg_annual_temp_stats$avg_cv_tmin,
    bsn_avg_mean_tmean= basin_stats$avg_annual_temp_stats$avg_mean_tmean,
    bsn_avg_sd_tmean  = basin_stats$avg_annual_temp_stats$avg_sd_tmean,
    bsn_avg_cv_tmean  = basin_stats$avg_annual_temp_stats$avg_cv_tmean,
    bsn_avg_mean_tmax = basin_stats$avg_annual_temp_stats$avg_mean_tmax,
    bsn_avg_sd_tmax   = basin_stats$avg_annual_temp_stats$avg_sd_tmax,
    bsn_avg_cv_tmax   = basin_stats$avg_annual_temp_stats$avg_cv_tmax,
    bsn_avg_cdd       = basin_stats$avg_annual_temp_stats$avg_cdd,
    bsn_avg_daily_range = basin_stats$avg_annual_temp_stats$avg_daily_range,
    
    bsn_avg_p5_doy  = basin_stats$percentile_dates$avg_p5_doy,
    bsn_avg_p25_doy = basin_stats$percentile_dates$avg_p25_doy,
    bsn_avg_p50_doy = basin_stats$percentile_dates$avg_p50_doy,
    bsn_avg_p75_doy = basin_stats$percentile_dates$avg_p75_doy,
    
    bsn_min_temp_date   = basin_stats$min_temp_date$avg_min_temp_doy,
    bsn_avg_cold7_doy   = basin_stats$coldest_7day_date$avg_cold7_doy,
    bsn_avg_hot_day_doy = basin_stats$hottest_day_date$avg_hot_day_doy,
    bsn_avg_hot7_doy    = basin_stats$hottest_7day_date$avg_hot7_doy,
    
    gage_avg_mean_tmin = gauge_stats$avg_annual_temp_stats$avg_mean_tmin,
    gage_avg_sd_tmin   = gauge_stats$avg_annual_temp_stats$avg_sd_tmin,
    gage_avg_cv_tmin   = gauge_stats$avg_annual_temp_stats$avg_cv_tmin,
    gage_avg_mean_tmean= gauge_stats$avg_annual_temp_stats$avg_mean_tmean,
    gage_avg_sd_tmean  = gauge_stats$avg_annual_temp_stats$avg_sd_tmean,
    gage_avg_cv_tmean  = gauge_stats$avg_annual_temp_stats$avg_cv_tmean,
    gage_avg_mean_tmax = gauge_stats$avg_annual_temp_stats$avg_mean_tmax,
    gage_avg_sd_tmax   = gauge_stats$avg_annual_temp_stats$avg_sd_tmax,
    gage_avg_cv_tmax   = gauge_stats$avg_annual_temp_stats$avg_cv_tmax,
    gage_avg_cdd       = gauge_stats$avg_annual_temp_stats$avg_cdd,
    gage_avg_daily_range = gauge_stats$avg_annual_temp_stats$avg_daily_range,
    
    gage_avg_p5_doy  = gauge_stats$percentile_dates$avg_p5_doy,
    gage_avg_p25_doy = gauge_stats$percentile_dates$avg_p25_doy,
    gage_avg_p50_doy = gauge_stats$percentile_dates$avg_p50_doy,
    gage_avg_p75_doy = gauge_stats$percentile_dates$avg_p75_doy,
    
    gage_min_temp_date   = gauge_stats$min_temp_date$avg_min_temp_doy,
    gage_avg_cold7_doy   = gauge_stats$coldest_7day_date$avg_cold7_doy,
    gage_avg_hot_day_doy = gauge_stats$hottest_day_date$avg_hot_day_doy,
    gage_avg_hot7_doy    = gauge_stats$hottest_7day_date$avg_hot7_doy
    )
    
  temp_stats_df <- rbind(temp_stats_df, row)
}

write.csv(temp_stats_df,
          "temperature_stats.csv",
          row.names = FALSE)

###############################################################################
# 9. Standardized Temperature Events & Gaussian Fit
###############################################################################

# Helper: count events ≥ min_duration
count_consecutive_events <- function(x, min_duration = 7) {
  r <- rle(x)
  sum(r$lengths[r$values] >= min_duration)
}

compute_standardized_temp_stats <- function(weather_ts, location = "gauge") {
  
  # Determine the appropriate column names for gauge series
  tmin_col  <- paste0(location, "_tasmin")
  tmean_col <- paste0(location, "_tmean")
  tmax_col  <- paste0(location, "_tasmax")
  
  # Standardize each temperature series over the entire timeseries period
  weather_ts <- weather_ts %>%
    mutate(
      st_tasmin = (get(tmin_col) - mean(get(tmin_col), na.rm = TRUE)) / sd(get(tmin_col), na.rm = TRUE),
      st_tmean = (get(tmean_col) - mean(get(tmean_col), na.rm = TRUE)) / sd(get(tmean_col), na.rm = TRUE),
      st_tasmax = (get(tmax_col) - mean(get(tmax_col), na.rm = TRUE)) / sd(get(tmax_col), na.rm = TRUE)
    ) %>%
    mutate(year = year(date),
           doy  = yday(date))
  
  # cool days are those with st_tasmin < -1.
  cool_daily <- weather_ts %>% mutate(cool = st_tasmin < -1)
  cool_counts <- cool_daily %>% 
    group_by(year) %>% 
    summarize(cool_days = sum(cool, na.rm = TRUE))
  
  # Count cool events: consecutive days where st_tasmin < -1 with duration >= 7.
  cool_events_yearly <- weather_ts %>% 
    group_by(year) %>% 
    summarize(cool_events = count_consecutive_events(st_tasmin < -1, min_duration = 7))
  
  avg_cool_days   <- mean(cool_counts$cool_days, na.rm = TRUE)
  avg_cool_events <- mean(cool_events_yearly$cool_events, na.rm = TRUE)
  
  # For tasmax: warm days are those with st_tasmax > 1.
  warm_daily <- weather_ts %>% mutate(warm = st_tasmax > 1)
  warm_counts <- warm_daily %>% 
    group_by(year) %>% 
    summarize(warm_days = sum(warm, na.rm = TRUE))
  
  warm_events_yearly <- weather_ts %>% 
    group_by(year) %>% 
    summarize(warm_events = count_consecutive_events(st_tasmax > 1, min_duration = 7))
  
  avg_warm_days   <- mean(warm_counts$warm_days, na.rm = TRUE)
  avg_warm_events <- mean(warm_events_yearly$warm_events, na.rm = TRUE)
  
  # For tasmin: cold events when st_tasmin < -1.5
  cold_stats <- weather_ts %>%
    group_by(year) %>%
    summarize(
      longest_cold = {
        r <- rle(st_tasmin < -1.5)
        if(any(r$values)) max(r$lengths[r$values]) else NA
      },
      avg_cold_length = {
        r <- rle(st_tasmin < -1.5)
        if(any(r$values)) mean(r$lengths[r$values]) else NA
      }
    )
  avg_longest_cold    <- mean(cold_stats$longest_cold, na.rm = TRUE)
  avg_cold_period_len <- mean(cold_stats$avg_cold_length, na.rm = TRUE)
  
  # Average gap between the two coldest days (lowest st_tasmin) per year.
  coldest_day_gap <- weather_ts %>%
    group_by(year) %>%
    summarize(
      gap = {
        order_idx <- order(st_tasmin)
        if(length(order_idx) >= 2) abs(doy[order_idx[2]] - doy[order_idx[1]]) else NA
      }
    )
  avg_coldest_day_gap <- mean(coldest_day_gap$gap, na.rm = TRUE)
  
  # Average gap between the two coldest 7-day periods.
  coldest7_gap <- weather_ts %>%
    group_by(year) %>%
    do({
      df <- .
      if(nrow(df) < 7) return(data.frame(cold7_gap = NA))
      roll_mean <- rollapply(df$st_tasmin, width = 7, FUN = mean, align = "center", fill = NA)
      valid_idx <- which(!is.na(roll_mean))
      if(length(valid_idx) < 2) return(data.frame(cold7_gap = NA))
      order_idx <- order(roll_mean[valid_idx])
      day1 <- df$doy[valid_idx][order_idx[1]]
      day2 <- df$doy[valid_idx][order_idx[2]]
      data.frame(cold7_gap = abs(day2 - day1))
    })
  avg_cold7_gap <- mean(coldest7_gap$cold7_gap, na.rm = TRUE)
  
  # For tasmax: hot events when st_tasmax > 1.5
  hot_stats <- weather_ts %>%
    group_by(year) %>%
    summarize(
      longest_hot = {
        r <- rle(st_tasmax > 1.5)
        if(any(r$values)) max(r$lengths[r$values]) else NA
      },
      avg_hot_length = {
        r <- rle(st_tasmax > 1.5)
        if(any(r$values)) mean(r$lengths[r$values]) else NA
      }
    )
  avg_longest_hot    <- mean(hot_stats$longest_hot, na.rm = TRUE)
  avg_hot_period_len <- mean(hot_stats$avg_hot_length, na.rm = TRUE)
  
  # Average gap between the two hottest days (highest st_tasmax)
  hottest_day_gap <- weather_ts %>%
    group_by(year) %>%
    summarize(
      gap = {
        order_idx <- order(-st_tasmax)
        if(length(order_idx) >= 2) abs(doy[order_idx[1]] - doy[order_idx[2]]) else NA
      }
    )
  avg_hottest_day_gap <- mean(hottest_day_gap$gap, na.rm = TRUE)
  
  # Average gap between the two hottest 7-day periods.
  hottest7_gap <- weather_ts %>%
    group_by(year) %>%
    do({
      df <- .
      if(nrow(df) < 7) return(data.frame(hot7_gap = NA))
      roll_mean <- rollapply(df$st_tasmax, width = 7, FUN = mean, align = "center", fill = NA)
      valid_idx <- which(!is.na(roll_mean))
      if(length(valid_idx) < 2) return(data.frame(hot7_gap = NA))
      order_idx <- order(-roll_mean[valid_idx])
      day1 <- df$doy[valid_idx][order_idx[1]]
      day2 <- df$doy[valid_idx][order_idx[2]]
      data.frame(hot7_gap = abs(day2 - day1))
    })
  avg_hot7_gap <- mean(hottest7_gap$hot7_gap, na.rm = TRUE)
  
  # Compute the average seasonal cycle from the gauge daily mean temperature.
  seasonal_cycle <- weather_ts %>%
    group_by(doy) %>%
    summarize(avg_tmean = mean(get(tmean_col), na.rm = TRUE))
  
  # Define the Gaussian function:
  gauss_fn <- function(d, a, b, c) {
    a * exp(-0.5 * ((d - c) / b)^2)
  }
  
  # Provide initial guesses:
  init_a <- max(seasonal_cycle$avg_tmean, na.rm = TRUE)
  init_c <- seasonal_cycle$doy[which.max(seasonal_cycle$avg_tmean)]
  init_b <- 50  # starting guess
  
  fit <- try(nlsLM(avg_tmean ~ a * exp(-0.5 * ((doy - c) / b)^2),
                   data = seasonal_cycle,
                   start = list(a = init_a, b = init_b, c = init_c),
                   lower = c(0, 0.1, 1),
                   upper = c(Inf, 100, 366),
                   control = nls.lm.control(maxiter = 200)),
             silent = TRUE)
  
  if (class(fit) == "try-error") {
    gauss_params <- c(a = NA, b = NA, c = NA)
  } else {
    gauss_params <- coef(fit)
  }
  
  # Return all computed attributes as a list
  result <- list(
    avg_annual_cool_days    = avg_cool_days,
    avg_annual_cool_events  = avg_cool_events,
    avg_annual_warm_days    = avg_warm_days,
    avg_annual_warm_events  = avg_warm_events,
    avg_longest_cold_duration = avg_longest_cold,
    avg_cold_period_length    = avg_cold_period_len,
    avg_coldest_day_gap       = avg_coldest_day_gap,
    avg_coldest7_day_gap      = avg_cold7_gap,
    avg_longest_hot_duration  = avg_longest_hot,
    avg_hot_period_length     = avg_hot_period_len,
    avg_hottest_day_gap       = avg_hottest_day_gap,
    avg_hottest7_day_gap      = avg_hot7_gap,
    gaussian_params           = gauss_params
  )
  
  return(result)
}

# Combine Attributes for All Stations into a Dataframe
std_temp_stats_df <- data.frame()

# Loop to build std_temp_stats_df and write to CSV (analogous to section 8)
for (station_id in names(station_info)) {
  
  cat("Computing standardized temperature stats for station:", station_id, "\n")
  ts_data <- read.csv(paste0("./hydrogfd_wsc/",
                             station_id,
                             "_hydrogfd.csv"))
  stats_gauge <- compute_standardized_temp_stats(ts_data, location = "gauge")
  stats_basin <- compute_standardized_temp_stats(ts_data, location = "basin")
  
  # Convert the list of stats into a data frame row
  row <- data.frame(
    station_id                    = station_id,
    
    gage_avg_annual_cool_days     = stats_gauge$avg_annual_cool_days,
    gage_avg_annual_cool_events   = stats_gauge$avg_annual_cool_events,
    gage_avg_annual_warm_days     = stats_gauge$avg_annual_warm_days,
    gage_avg_annual_warm_events   = stats_gauge$avg_annual_warm_events,
    gage_avg_longest_cold_duration = stats_gauge$avg_longest_cold_duration,
    gage_avg_cold_period_length    = stats_gauge$avg_cold_period_length,
    gage_avg_coldest_day_gap       = stats_gauge$avg_coldest_day_gap,
    gage_avg_coldest7_day_gap      = stats_gauge$avg_coldest7_day_gap,
    gage_avg_longest_hot_duration  = stats_gauge$avg_longest_hot_duration,
    gage_avg_hot_period_length     = stats_gauge$avg_hot_period_length,
    gage_avg_hottest_day_gap       = stats_gauge$avg_hottest_day_gap,
    gage_avg_hottest7_day_gap      = stats_gauge$avg_hottest7_day_gap,
    gage_gaussian_a              = stats_gauge$gaussian_params["a"],
    gage_gaussian_b              = stats_gauge$gaussian_params["b"],
    gage_gaussian_c              = stats_gauge$gaussian_params["c"],
    
    bsn_avg_annual_cool_days     = stats_basin$avg_annual_cool_days,
    bsn_avg_annual_cool_events   = stats_basin$avg_annual_cool_events,
    bsn_avg_annual_warm_days     = stats_basin$avg_annual_warm_days,
    bsn_avg_annual_warm_events   = stats_basin$avg_annual_warm_events,
    bsn_avg_longest_cold_duration = stats_basin$avg_longest_cold_duration,
    bsn_avg_cold_period_length    = stats_basin$avg_cold_period_length,
    bsn_avg_coldest_day_gap       = stats_basin$avg_coldest_day_gap,
    bsn_avg_coldest7_day_gap      = stats_basin$avg_coldest7_day_gap,
    bsn_avg_longest_hot_duration  = stats_basin$avg_longest_hot_duration,
    bsn_avg_hot_period_length     = stats_basin$avg_hot_period_length,
    bsn_avg_hottest_day_gap       = stats_basin$avg_hottest_day_gap,
    bsn_avg_hottest7_day_gap      = stats_basin$avg_hottest7_day_gap,
    bsn_gaussian_a              = stats_basin$gaussian_params["a"],
    bsn_gaussian_b              = stats_basin$gaussian_params["b"],
    bsn_gaussian_c              = stats_basin$gaussian_params["c"],
    
    stringsAsFactors        = FALSE
  )
  
  std_temp_stats_df <- rbind(std_temp_stats_df, row)
}

write.csv(std_temp_stats_df,
          "temperature_stats_std.csv",
          row.names = FALSE)

###############################################################################
# 10. Flow Statistics: L‐moments, AR(1), Seasonal Fit
###############################################################################

# Decimal year & fraction helpers
decimal_year <- function(date) {
  y <- year(date)
  doy <- yday(date)
  total_days <- ifelse(leap_year(date), 366, 365)
  return(y + (doy - 1) / total_days)
}

fractional_year <- function(date) {
  dec <- decimal_year(date)
  return(dec - floor(dec))
}


# Robust AR(1) estimation function
compute_ar1 <- function(x) {
  # Remove any NAs
  x <- as.vector(na.omit(x))
  n <- length(x)
  if(n < 2) return(NA)  # Not enough data
  
  # Try fitting an AR(1) model
  ar1 <- tryCatch({
    model <- arima(x, order = c(1, 0, 0))
    model$coef["ar1"]
  }, error = function(e) {
    # Fallback: compute lag-1 correlation
    cor(x[-n], x[-1], use = "complete.obs")
  })
  
  return(ar1)
}

# Initialize an empty dataframe to store flow attributes for each station
flow_attributes <- data.frame()

# Loop over each station
for (station in names(station_info)) {
  
  cat("Processing flow data for station:", station, "\n")
  
  # Retrieve daily flow data for the period 1994-2016 using tidyhydat.
  flow_data <- try(hy_daily_flows(station_number = station,
                            start_date = "1994-01-01",
                            end_date   = "2016-12-31"),
                   silent = TRUE)
  
  # Compute L‐moments
  lmoments <- try(samlmu(flow_data$Value), silent = TRUE)
  if (inherits(lmoments, "try-error") || any(is.na(lmoments))) {
    l_mean <- NA
    l_cv   <- NA
    l_skew <- NA
    l_kurt <- NA
  } else {
    l_mean <- lmoments[1]
    l_cv   <- lmoments[2]
    l_skew <- lmoments[3]
    l_kurt <- lmoments[4]
  }
  
  # Deseasonalize by month, standardize, compute AR1
  std_flow <- flow_data
  for (m in 1:12) {
    # Deseasonalize by subtracting the long-term monthly mean flow
    std_flow$Value[month(std_flow$Date) == m] <- std_flow$Value[month(std_flow$Date) == m] -
                                           mean(std_flow$Value[month(std_flow$Date) == m], na.rm = TRUE)
  }
  
  # Then standardize to mean 0 and SD 1
  std_flow$Value <- scale(std_flow$Value)
  
  ar1 <- compute_ar1(std_flow$Value)
  
  # Fit seasonal model: sin/cos on frac_year
  mean_flow <- mean(flow_data$Value, na.rm = TRUE)
  sd_flow   <- sd(flow_data$Value, na.rm = TRUE)
  flow_data <- flow_data %>% mutate(standardized_flow = (Value - mean_flow) / sd_flow)
  
  # Use the fractional part of the decimal year.
  flow_data <- flow_data %>% mutate(frac_year = fractional_year(Date))
  
  # Fit the seasonal model:
  seasonal_fit <- try(lm(standardized_flow ~ sin(2 * pi * frac_year) + cos(2 * pi * frac_year),
                         data = flow_data),
                      silent = TRUE)
  if (inherits(seasonal_fit, "try-error")) {
    a_coef <- NA
    b_coef <- NA
  } else {
    coefs <- coef(seasonal_fit)
    a_coef <- coefs["sin(2 * pi * frac_year)"]
    b_coef <- coefs["cos(2 * pi * frac_year)"]
  }
  
  # Compute amplitude, phase
  amplitude <- sqrt(a_coef^2 + b_coef^2)
  phase <- if (!is.na(a_coef) && !is.na(b_coef)) atan2(-a_coef, b_coef) else NA
  
  row <- data.frame(
    station_id = station,
    l_mean     = l_mean,
    l_cv       = l_cv,
    l_skew     = l_skew,
    l_kurt     = l_kurt,
    ar1        = ar1,
    amplitude  = amplitude,
    phase      = phase,
    stringsAsFactors = FALSE
  )
  
  # Append to flow_attributes
  flow_attributes <- rbind(flow_attributes, row)
}

# Save the final dataframe to a CSV file.
write.csv(flow_attributes,
          "flow_stats.csv",
          row.names = FALSE)

###############################################################################
# 11. Water Temperature Gaussian Fit
###############################################################################

wt_data <- read.csv("/water_temp_mean.csv") # mean daily water temperatures

# Initialize an empty dataframe to store wt attributes for each station
wt_attributes <- data.frame()

for (stn in names(wt_data)) {
  
  if (substr(stn,2,99) %in% names(station_info)){
    
    cat("Processing wt data for station:", substr(stn,2,99), "\n")
    
    wt_gauge <- wt_data[c("date", stn)]
    
    wt_gauge <- wt_gauge %>%
      mutate(year = year(date),
             doy  = yday(date))
    
    seasonal_cycle <- wt_gauge %>%
      group_by(doy) %>%
      summarize(avg_tmean = mean(get(stn), na.rm = TRUE))
    
    # Define the Gaussian function:
    gauss_fn <- function(d, a, b, c) {
      a * exp(-0.5 * ((d - c) / b)^2)
    }
    
    # Provide initial guesses:
    init_a <- max(seasonal_cycle$avg_tmean, na.rm = TRUE)
    init_c <- seasonal_cycle$doy[which.max(seasonal_cycle$avg_tmean)]
    init_b <- 50  # A rough guess
    
    fit <- try(nlsLM(avg_tmean ~ a * exp(-0.5 * ((doy - c) / b)^2),
                     data = seasonal_cycle,
                     start = list(a = init_a, b = init_b, c = init_c),
                     lower = c(0, 0.1, 1),
                     upper = c(Inf, 100, 366),
                     control = nls.lm.control(maxiter = 200)),
               silent = TRUE)
    
    if (class(fit) == "try-error") {
      gauss_params <- c(a = NA, b = NA, c = NA)
    } else {
      gauss_params <- coef(fit)
    }
    
    row <- data.frame(
      station_id      = substr(stn,2,99),
      wt_gaussian_a  = gauss_params["a"],
      wt_gaussian_b  = gauss_params["b"],
      wt_gaussian_c  = gauss_params["c"],
      stringsAsFactors = FALSE
    )
    
    wt_attributes <- rbind(wt_attributes, row)
  }
}

# Save the final dataframe to a CSV file.
write.csv(wt_attributes,
          "wt_stats.csv",
          row.names = FALSE)

###############################################################################
# 12. Basin Lake‐Area Percentage (LakeATLAS)
###############################################################################

# Read the lake dataset
lakes <- st_read("./LakeATLAS_v10_pol.shp", quiet = TRUE) # lake atlas
lakes <- st_make_valid(lakes)
lakes <- st_sf(lakes, agr = "constant")

# Initialize a vector to hold the percentage of lake area for each station.
perc_lake_area <- numeric(length(station_info))
names(perc_lake_area) <- names(station_info)

# Loop over each station to compute lake area percentage.
for (station in names(station_info)[326:2213]) {
  cat("Processing lake data for station:", station, "\n")
  
  # Read the basin polygon for this station.
  basin <- st_read(station_info[[station]]$basin_shp, quiet = TRUE)
  
  basin <- st_make_valid(basin)
  
  # Reproject basin if its CRS does not match lakes.
  if (st_crs(basin) != st_crs(lakes)) {
    basin <- st_transform(basin, st_crs(lakes))
  }
  
  # Compute basin area (using st_area, returns in square meters if CRS is in meters)
  basin_area <- st_area(basin)
  
  # Now, compute the intersection between the candidate lakes and the basin.
  lakes_in_basin <- st_intersection(lakes, basin)
  
  # If no lakes are found, assign 0%.
  if (nrow(lakes_in_basin) == 0) {
    perc_lake_area[station] <- 0
  } else {
    total_lake_area <- sum(st_area(lakes_in_basin))
    perc_lake_area[station] <- as.numeric(total_lake_area / basin_area * 100)
  }
}

# Create a dataframe of the lake area percentages.
df_lake <- data.frame(
  station_id = names(perc_lake_area),
  perc_lake_area = perc_lake_area,
  stringsAsFactors = FALSE
)

# Save the final dataframe to a CSV file.
write.csv(df_lake,
          "basin_lake_stats.csv",
          row.names = FALSE)

###############################################################################
# 13. Merge All Attribute Tables & Save Master CSV
###############################################################################

att_stn   <- read.csv("station_properties.csv")
att_lake  <- read.csv("basin_lake_stats.csv")
att_dem   <- read.csv("canadian_dem_attributes.csv")
att_lc    <- read.csv("canadian_lc_attributes.csv")
att_flow  <- read.csv("flow_stats.csv")
att_temp  <- read.csv("temperature_stats.csv")
att_stemp <- read.csv("temperature_stats_std.csv")
att_wt    <- read.csv("wt_stats.csv")

all_attributes <- att_stn
all_attributes <- merge(all_attributes, att_dem, by   = "station_id")
all_attributes <- merge(all_attributes, att_lc, by    = "station_id")
all_attributes <- merge(all_attributes, att_lake, by  = "station_id")
all_attributes <- merge(all_attributes, att_flow, by  = "station_id")
all_attributes <- merge(all_attributes, att_temp, by  = "station_id")
all_attributes <- merge(all_attributes, att_stemp, by = "station_id")
all_attributes <- merge(all_attributes, att_wt, by    = "station_id", all.x = TRUE)

write.csv(all_attributes,
          "all_gauge_Attributes.csv",
          row.names = FALSE)

###############################################################################
# 14. Random Forest Modeling & Importance Extraction
###############################################################################

set.seed(42)
# Keep only gauges that have wt data (i.e. non-NA for at least one wt parameter)
data_rf <- all_attributes %>% 
  filter(!is.na(wt_gaussian_a) & !is.na(wt_gaussian_b) & !is.na(wt_gaussian_c))


# Exclude station_id and water temperature Gaussian parameters from predictors
predictor_cols <- setdiff(names(data_rf), c("station_id", 
                                            "wt_gaussian_a", "wt_gaussian_b", "wt_gaussian_c",
                                            "land_class_3", "land_class_4", "land_class_7",
                                            "land_class_9")) # remove some lc attributes with 0 values

# Remove all predictors that start with "bsn_", determined through testing
predictor_cols <- predictor_cols[!grepl("^bsn_", predictor_cols)]

response_vars <- c("wt_gaussian_a", "wt_gaussian_b", "wt_gaussian_c")

# Fit Random Forest models for each water temperature parameter
rf_models <- list()
importance_list <- list()

for (resp in response_vars) {
  cat("Fitting RF for", resp, "\n")
  rf_model <- randomForest(x = data_rf[, predictor_cols],
                           y = data_rf[[resp]],
                           importance = TRUE)
  rf_models[[resp]] <- rf_model
  importance_list[[resp]] <- importance(rf_model)
}

# Set the cumulative importance threshold (e.g., 70%)
importance_threshold <- 0.7

# Function to get top predictors that sum to at least the given threshold
get_top_predictors <- function(imp_vec, threshold = 0.7) {
  # Sort in descending order
  imp_sorted <- sort(imp_vec, decreasing = TRUE)
  total_imp <- sum(imp_sorted)
  cum_imp <- cumsum(imp_sorted)
  # Find the smallest set where cumulative importance ratio exceeds threshold.
  num_to_keep <- which(cum_imp/total_imp >= threshold)[1]
  names(imp_sorted)[1:num_to_keep]
}

# Get predictor lists for each water temperature response
important_predictors_list <- list()

for (resp in response_vars) {
  # Extract the %IncMSE values
  imp <- rf_models[[resp]][["importance"]][,1]
  top_preds <- get_top_predictors(imp, threshold = importance_threshold)
  important_predictors_list[[resp]] <- top_preds
  
  cat("For", resp, "the top predictors (cumulative importance >=", importance_threshold*100, "%) are:\n")
  print(top_preds)
  cat("\n")
}

#--------------------------------------------------------------------
# some manual work Remove Highly Correlated Predictors Among the Top Predictors
#--------------------------------------------------------------------
final_predictors <- unique(unlist(important_predictors_list))

# Compute the correlation matrix among the top predictors
corr_matrix <- cor(data_rf[, final_predictors], use = "complete.obs")

# Manually Identify predictors with correlation above the threshold 0.7
final_predictors <- c("gage_gaussian_b", "gage_gaussian_a",
                      "perc_lake_area", "dem_avg_slope", "lon",
                      "land_class_13", "gage_avg_cv_tmean",
                      "gage_avg_hot_period_length", "ar1",
                      "gage_avg_cv_tmax", "l_cv",
                      "amplitude", "land_class_11",
                      "land_class_15", "land_class_17",
                      "l_skew", "land_class_19",
                      "land_class_14", "gage_avg_hot_day_doy") # top 70% C_1

final_predictors <- c("gage_gaussian_a", "gage_gaussian_c") # chu 2010 C_2

final_predictors <- c("gage_gaussian_a", "gage_gaussian_c",
                      "perc_lake_area", "l_cv",
                      "land_class_1", "land_class_2",
                      "land_class_5", "land_class_6") # chu 2010 C_3

final_predictors <- c("lon", "lat", "basin_area", "dem_avg_slope", 
                      "dem_mean", "gage_avg_mean_tmin", "land_class_2",
                      "land_class_5", "land_class_6") # daigle 2019 C_5

final_predictors <- c("gage_gaussian_a", "gage_gaussian_b", "gage_gaussian_c",
                      "l_mean", "dem_median", "perc_lake_area") # garner 2013 C_4

final_predictors <- c("land_class_6", "ar1", "land_class_14", 
                      "land_class_11", "l_skew", "gage_avg_cv_tmax", 
                      "land_class_13", "dem_range", "gage_min_temp_date", 
                      "land_class_5", "gage_avg_hot_day_doy", 
                      "gage_avg_cv_tmean", "gage_gaussian_a", "gage_gaussian_b", 
                      "land_class_2", "gage_avg_annual_cool_events") # random 1 C_6

final_predictors <- c("lon", "dem_range", "land_class_19", "land_class_12", 
                      "gage_avg_sd_tmin", "land_class_6", "gage_avg_hot_period_length", 
                      "land_class_5", "land_class_18") # random from top 70% C_7

final_predictors <- c("lon", "lat", "land_class_1", "land_class_2",
                      "land_class_5", "land_class_6", "land_class_11", "land_class_12",
                      "land_class_13", "land_class_14", "land_class_15", "land_class_16",
                      "land_class_17", "land_class_19", "perc_lake_area", "l_mean",
                      "gage_gaussian_a", "gage_gaussian_b", "gage_avg_hot_period_length") # hand picked C_8

n <- sum(!is.na(all_attributes$wt_gaussian_a))

cluster_data <- all_attributes[is.na(all_attributes$wt_gaussian_a), ]
cluster_data <- rbind(all_attributes[!is.na(all_attributes$wt_gaussian_a), ],
                      cluster_data)

cluster_data[-1] <- scale(cluster_data[-1])


cluster_labels <-  data.frame(matrix(nrow=nrow(cluster_data), ncol=100))
cluster_sil <-  data.frame(matrix(nrow=nrow(cluster_data), ncol=100))

c <- 11

for (i in 1:100) {
  print(i)
  set.seed(i)
  rf <- randomForest(x = cluster_data[final_predictors],
                     subset=seq(1:nrow(cluster_data)) <= n,
                     ntree=9000,
                     proximity = TRUE,
                     oob.prox = TRUE)
  
  rf_pam <- pam(rf$proximity[1:n, 1:n], c)
  
  mediod_stns <- rf_pam$id.med
  
  rf_pam <- pam(rf$proximity, c, medoids=mediod_stns, do.swap = FALSE)
  
  
  cluster_labels[, i] <- rf_pam$clustering
  temp <- cbind(id = as.numeric(row.names(rf_pam$silinfo$widths)), rf_pam$silinfo$widths)
  temp <- temp[order(temp[,1], decreasing=FALSE),]
  cluster_sil[, i] <- temp[, 4]
}


cluster_labels_final <-  data.frame(matrix(nrow=nrow(cluster_data), ncol=100))

mode <- function(x) {
  ux <- unique(x)
  ux[which.max(tabulate(match(x, ux)))]
}

all_clusters_clean <- cluster_labels

# get initial stability
stability <- mean(apply(all_clusters_clean, 1, function(x) sum(x == mode(x))))

# greedy approach to making labels consistent
for (ii in 1:100) {
  print(ii)
  for (i in 1:c) {
    
    ids <- which(all_clusters_clean[,ii] == i)
    
    for (j in 1:ncol(cluster_labels)) {
      a <- as.data.frame(table(all_clusters_clean[ids, j]))
      a$Var1 <- as.numeric(levels(a$Var1))[as.integer(a$Var1)]
      
      for (k in 1:nrow(a)) {
        cluster_try <- all_clusters_clean
        
        cluster_try[cluster_try[,j]==a[k, 1], j] <- 100
        cluster_try[cluster_try[,j]==i, j] <- a[k, 1]
        cluster_try[cluster_try[,j]==100, j] <- i
        
        stability2 <- mean(apply(cluster_try, 1, function(x) sum(x == mode(x))))
        
        if (stability2 > stability) {
          stability <- stability2
          all_clusters_clean <- cluster_try
        }
      }
    }
  }
}

for (s in 1:100){
  for (i in 1:c){
    cluster_labels_final[i, s] = all_clusters_clean[cluster_labels[1:nrow(cluster_labels),s]==i, s][1]
  }
}

for (s in 1:100){
  for (i in 1:c){
    cluster_labels[cluster_labels[,s]==i, s] <- 100+i
  }
  
  for (i in 1:c){
    cluster_labels[cluster_labels[,s]==100+i, s] <- cluster_labels_final[i, s]
  }
}

cluster_labels$station_id <- cluster_data$station_id
cluster_sil$station_id <- cluster_data$station_id

write.csv(cluster_labels, paste0("cluster_groups_name.csv"))
write.csv(cluster_sil, paste0("cluster_sil_name.csv"))


###############################################################################
# End of Script
###############################################################################

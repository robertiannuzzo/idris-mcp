module Interactive.Meteorology

import Interactive.Meteorology.Locale
import Data.List.Quantifiers
import Data.Singleton

OneOf : List String -> Type
OneOf = Any Singleton

-- https://api.openweathermap.org/data/3.0/onecall?lat={lat}&lon={lon}&exclude={part}&appid={API key}
Latitude, Longitude : Type
Latitude = Double
Longitude = Double

Exclusions : Type
Exclusions = List (OneOf
  [ "current"
  , "minutely"
  , "hourly"
  , "daily"
  , "alerts"
  ])

data Units = Standard | Metric | Imperial

record Request where
  lat : Latitude
  lon : Longitude
  appid : String
  exclude : Maybe Exclusions
  units : Maybe Units
  lang : Maybe Locale
record Alerts where-- National weather alerts data from major national weather warning systems
  sender_name : String -- Name of the alert source. Please read here the full list of alert sources
  event : String -- Alert event name
  start : Date -- Date and time of the start of the alert, Unix, UTC
  end : Date -- Date and time of the end of the alert, Unix, UTC
  description : String -- Description of the alert
  tags : String

record Weather where
  id : String -- Weather condition id
  main : WeatherGroup -- Group of weather parameters (Rain, Snow etc.)
  description : String -- Weather condition within the group (full list of weather conditions). Get the output in your language
  icon : String -- Weather icon id. How to get icons

record Forecast where
  dt : Date
  sunrise : Date
  sunset : Date
  temp : Temp
  feels_like : Temp -- This temperature parameter accounts for the human perception of weather. Units – default: kelvin, metric: Celsius, imperial: Fahrenheit.
  pressure : HectoPascal -- Atmospheric pressure on the sea level, hPa
  humidity : Percent -- Humidity, %
  dew_point : Temp -- Atmospheric temperature (varying according to pressure and humidity) below which water droplets begin to condense and dew can form. Units – default: kelvin, metric: Celsius, imperial: Fahrenheit
  clouds : Percent -- Cloudiness, %
  uvi : String -- Current UV index.
  visibility : Metre -- Average visibility, metres. The maximum value of the visibility is 10 km
  wind_speed : Speed -- Wind speed. Wind speed. Units – default: metre/sec, metric: metre/sec, imperial: miles/hour. How to change units used
  wind_gust : Speed -- (where available) Wind gust. Units – default: metre/sec, metric: metre/sec, imperial: miles/hour. How to change units used
  wind_deg : Degree -- Wind direction, degrees (meteorological)
  -- field 1h of object at `rain`
  rain : Maybe MiliPerHour -- (where available) Precipitation, mm/h. Please note that only mm/h as units of measurement are available for this parameter
  -- field 1h of object at `snow`
  snow : Maybe MiliPerHour -- (where available) Precipitation, mm/h. Please note that only mm/h as units of measurement are available for this parameter
  weather : Weather

record Response (req : Request) where
  let
    Temp : Type
    Temp = Temperature req.unit
    Speed : Type
    Speed = DistancePerTime req.unit

  lat : Latitude
  lon : Longitude
  timezone : Timezone
  timezone_offset : Seconds
  current : WeatherData
  minutely Minute forecast weather data API response
  minutely.dt : Date --  Time of the forecasted data, unix, UTC
  minutely.precipitation : MiliPerHour -- Precipitation, mm/h. Please note that only mm/h as units of measurement are available for this parameter
  hourly : WeatherData -- Hourly forecast weather data API response
  daily : WeatherData -- Daily forecast weather data API response
  alerts : Alerts

# Find Boolector.
#  Boolector_FOUND       - System has Boolector library
#  Boolector_INCLUDE_DIR - Boolector include directory
#  Boolector_LIBRARIES   - Libraries needed to use Boolector

if(NOT Boolector_HOME)
  set(Boolector_HOME ${PROJECT_SOURCE_DIR}/solvers/boolector/build/install)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(Boolector_INCLUDE_DIR
  NAMES boolector.h
  PATHS ${Boolector_HOME}/include
  NO_DEFAULT_PATH
)

find_library(Boolector_LIBRARIES
  NAMES boolector
  PATHS ${Boolector_HOME}/lib
  NO_DEFAULT_PATH
)

if(CHECK_SYSTEM_VERSION)
  find_path(Boolector_INCLUDE_DIR NAMES boolector.h)
  find_library(Boolector_LIBRARIES NAMES boolector)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Boolector
  DEFAUlT_MSG
  Boolector_INCLUDE_DIR
  Boolector_LIBRARIES
)

mark_as_advanced(
  Boolector_INCLUDE_DIR
  Boolector_LIBRARIES
)

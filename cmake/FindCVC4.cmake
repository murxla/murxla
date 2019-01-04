# Find CVC4.
#  CVC4_FOUND       - System has CVC4 library
#  CVC4_INCLUDE_DIR - CVC4 include directory
#  CVC4_LIBRARIES   - Libraries needed to use CVC4

if(NOT CVC4_HOME)
  set(CVC4_HOME ${PROJECT_SOURCE_DIR}/deps)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(CVC4_INCLUDE_DIR
  NAMES api/cvc4cpp.h
  PATHS ${CVC4_HOME}/include
  NO_DEFAULT_PATH
)

find_library(CVC4_LIBRARIES
  NAMES cvc4
  PATHS ${CVC4_HOME}/lib
  NO_DEFAULT_PATH
)

if(CHECK_SYSTEM_VERSION)
  find_path(CVC4_INCLUDE_DIR NAMES cvc4/api/cvc4cpp.h)
  find_library(CVC4_LIBRARIES NAMES cvc4)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CVC4
  DEFAUlT_MSG
  CVC4_INCLUDE_DIR
  CVC4_LIBRARIES
)

mark_as_advanced(
  CVC4_INCLUDE_DIR
  CVC4_LIBRARIES
)

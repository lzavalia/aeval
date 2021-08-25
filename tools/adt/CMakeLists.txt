add_executable (ind Adt.cpp)
target_link_libraries (ind ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS ind RUNTIME DESTINATION bin)

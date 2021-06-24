add_executable (pde Pde.cpp)
target_link_libraries (pde ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS pde RUNTIME DESTINATION bin)

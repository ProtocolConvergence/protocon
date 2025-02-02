if (OPENMP_FOUND)
  add_test(NAME OpenMP_LeaderRingHuang_test COMMAND ${Protocon_EXECUTABLE}
    -parallel 4
    -x "${PROJECT_SOURCE_DIR}/examplespec/LeaderRingHuang.prot"
    -prep-conflicts
  )
  set_tests_properties(OpenMP_LeaderRingHuang_test PROPERTIES PROCESSORS 4)
endif()

if (MPI_FOUND)
  add_test(NAME MPI_LeaderRingHuang_test COMMAND ${MPIEXEC}
    ${MPIEXEC_NUMPROC_FLAG} 4
    ${MPIEXEC_PREFLAGS}
    # --use-hwthread-cpus
    "$<TARGET_FILE:protocon-mpi>"
    ${MPIEXEC_POSTFLAGS}
    -x "${PROJECT_SOURCE_DIR}/examplespec/LeaderRingHuang.prot"
    -prep-conflicts
  )
  set_tests_properties(MPI_LeaderRingHuang_test PROPERTIES PROCESSORS 4)
endif()

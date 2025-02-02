if (MPI_FOUND)
  set(host_process_count 4)
  if (${MPIEXEC_MAX_NUMPROCS} LESS ${host_process_count})
    set(host_process_count ${MPIEXEC_MAX_NUMPROCS})
  endif()
  add_test(NAME MPI_LeaderRingHuang_test COMMAND ${MPIEXEC}
    ${MPIEXEC_NUMPROC_FLAG} ${host_process_count}
    # --use-hwthread-cpus
    ${MPIEXEC_PREFLAGS}
    "$<TARGET_FILE:protocon-mpi>"
    ${MPIEXEC_POSTFLAGS}
    -x "${PROJECT_SOURCE_DIR}/examplespec/LeaderRingHuang.prot"
    -prep-conflicts
  )
  set_tests_properties(MPI_LeaderRingHuang_test PROPERTIES
    PROCESSORS ${host_process_count}
  )
endif()

if (OPENMP_FOUND)
  add_test(NAME OpenMP_LeaderRingHuang_test COMMAND ${Protocon_EXECUTABLE}
    -parallel 4
    -x "${PROJECT_SOURCE_DIR}/examplespec/LeaderRingHuang.prot"
    -prep-conflicts
  )
  set_tests_properties(OpenMP_LeaderRingHuang_test PROPERTIES PROCESSORS 4)
endif()

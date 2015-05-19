
# Make sure we have required input
foreach(vbl protocon_exe xfile)
  if(NOT DEFINED ${vbl})
    message(FATAL_ERROR "'${vbl}' must be defined on the command line")
  endif()
endforeach()

# Execute the test
execute_process (
  COMMAND ${protocon_exe} -nop -x ${xfile} -o -
  COMMAND ${protocon_exe} -verify -x -
  RESULT_VARIABLE istat
  )

# Check its return status
if (istat)
  message (FATAL_ERROR "'${protocon_exe}' failed")
endif ()



# Releasing a New Version

The version number is today's date.
This can be overridden in the top-level `CMakeLists.txt` (a commented line shows how).

```shell
# Always release from a clean source tree.
# The "protocon_to_release" directory name is not important.
git clone https://github.com/grencez/protocon.git protocon_to_release
cd protocon_to_release
mkdir bld
# Configure.
cmake ..
# Build.
make
# Test. Only proceed if all of them pass.
ctest
# Package.
cpack
ls -lh protocon-*.zip
```

You should have a `.zip` file in the `bld` directory that matches the `protocon-*.zip` glob.
Ship it!


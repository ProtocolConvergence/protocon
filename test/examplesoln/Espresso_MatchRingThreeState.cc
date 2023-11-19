#include <fildesh/istream.hh>
#include <fildesh/ostream.hh>

int main() {
  // Read everything.
  slurp_FildeshX(fildesh::ifstream("/dev/stdin").c_struct());
  // Write everything.
  fildesh::ofstream("/dev/stdout") << "\
## Process P[i]:\n\
# m[i-1] m[i] m[i+1] m[i]'\n\
.mv 4 0 3 3 3 3\n\
.p 3\n\
 001 011 011 100\n\
 110 101 001 010\n\
 110 110 110 001\n\
.e\n\
";
  return 0;
}

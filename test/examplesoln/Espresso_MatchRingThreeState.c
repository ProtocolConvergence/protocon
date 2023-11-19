#include <fildesh/fildesh.h>

int main() {
  static const char content[] = "\
## Process P[i]:\n\
# m[i-1] m[i] m[i+1] m[i]'\n\
.mv 4 0 3 3 3 3\n\
.p 3\n\
 001 011 011 100\n\
 110 101 001 010\n\
 110 110 110 001\n\
.e\n";
  FildeshO* out;
  FildeshX* in = open_FildeshXF("/dev/stdin");
  slurp_FildeshX(in);
  close_FildeshX(in);
  out = open_FildeshOF("/dev/stdout");
  put_bytestring_FildeshO(out, fildesh_bytestrlit(content));
  close_FildeshO(out);
  return 0;
}

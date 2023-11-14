// #include <fildesh/string.hh>

static inline
  bool
slurp_file_to_string(std::string& text, const char* filename)
{
  text.clear();
  FildeshX* in = open_FildeshXF(filename);
  bool good = false;
  if (in) {
    if (slurp_FildeshX(in)) {
      text = fildesh::make_string_view(*in);
      good = true;
    }
  }
  close_FildeshX(in);
  return good;
}

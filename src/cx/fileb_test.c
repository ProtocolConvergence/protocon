/**
 * \file fileb_test.c
 * Tests for buffered files.
 **/

#include "syscx.h"

#include "alphatab.h"
#include "fileb.h"


/** \test
 * Test FileB ability to skip whitespace.
 * This also shows how FileB overlays work.
 **/
  void
testfn_skipws_FileB ()
{
  const char text[] = "hello i am\n some \n text! ";
  const char* const expect_text[] = {
    "hello", "i", "am", "some", "text!"
  };
  uint idx = 0;
  XFileB xfb[] = {DEFAULT_XFileB};
  XFile* xf = &xfb->xf;
  OFile* of = stderr_OFile ();
  char* s;

#if 0
  open_FileB (&xfb, "", "test");
#else
  SizeTable (xf->buf, sizeof(text));
  memcpy (xf->buf.s, text, xf->buf.sz);
#endif

  for (s = getline_XFile (xf);
      s;
      s = getline_XFile (xf))
  {
    XFile olay[1];
    olay_txt_XFile (olay, xf, IdxEltTable( xf->buf, s ));

    for (s = nextok_XFile (olay, 0, 0);
        s;
        s = nextok_XFile (olay, 0, 0))
    {
      oput_cstr_OFile (of, s);
      oput_char_OFile (of, '\n');
      flush_OFile (of);
      Claim2(idx ,<, ArraySz( expect_text ));
      Claim( eq_cstr (expect_text[idx], s) );
      ++ idx;
    }
  }

  lose_XFileB (xfb);
  oput_cstr_OFile (of, "------------\n");
  flush_OFile (of);
}

static
  void
testfn_pathname ()
{
  typedef struct TestCase TestCase;
  struct TestCase {
    const char* opt_dir;
    const char* filename;
    const char* expect;
  };
  const TestCase tests[] =
  {  { "my/path", "/oh/no/abs/file.txt", "/oh/no/abs/file.txt" }
    ,{ "my/path", "oh/no/abs/file.txt", "my/path/oh/no/abs/file.txt" }
    ,{ 0, "path/to/file.txt", "path/to/file.txt" }
    ,{ 0, "file.txt", "file.txt" }
    ,{ "", "file.txt", "file.txt" }
    ,{ "path", "file.txt", "path/file.txt" }
    ,{ "path/", "file.txt", "path/file.txt" }
    ,{ "/", "path/to/file.txt", "/path/to/file.txt" }
    ,{ "/path", "to/file.txt", "/path/to/file.txt" }
    ,{ "/path/", "to/file.txt", "/path/to/file.txt" }
  };
  uint i;

  UFor( i, ArraySz( tests ) ) {
    const TestCase testcase = tests[i];
    AlphaTab result = DEFAULT_AlphaTab;
    uint sepidx =
      pathname2_AlphaTab (&result, testcase.opt_dir, testcase.filename);

    if (!eq_cstr (result.s, testcase.expect) ) {
      fprintf (stderr, "opt_dir: %s  filename: %s  expect: %s  result: %s\n",
          testcase.opt_dir ? "(NULL)" : testcase.opt_dir,
          testcase.filename,
          testcase.expect,
          result.s);
      Claim( 0 );
    }

    if (sepidx != 0 && '/' != result.s[sepidx-1]) {
      result.s[sepidx-1] = '\0';
      fprintf (stderr, "dir:%s  file:%s\n",
          result.s,
          &result.s[sepidx]);
      Claim2( '/' ,==, result.s[sepidx-1] );
    }

    lose_AlphaTab (&result);
  }
}


int main(int argc, char** argv)
{
  int argi = init_sysCx (&argc, &argv);
  (void) argi;

  testfn_skipws_FileB();
  testfn_pathname();

  lose_sysCx ();
  return 0;
}

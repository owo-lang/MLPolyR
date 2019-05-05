# include <stdio.h>
# include <stdlib.h>
# include <string.h>
# include <stdarg.h>


# define HEAPSIZE (16*1024*1024/4)	 /* 16 MB in words */


# define BUFSZ 128

extern int mlpr_entrypoint (void *, void *, void *, void *);

extern unsigned mlpr_frame_info_table[];
extern unsigned *mlpr_limit_ptr;
extern unsigned *mlpr_main_stack_ptr;

#define tptr(p) ((void*)(((char*)(void*)(p))+1))
#define taddr(x) tptr(&(x))
#define untag(x,t) ((t*)(((char*)(void*)(x))-1))

#define boxInt(i) ((i)<<1)
#define unboxInt(i) ((i)>>1)
#define isInt(x) (((x) & 0x1) == 0)

static unsigned int
  *to_space_ptr         = NULL,
  *from_space_ptr       = NULL,
  *from_space_ptr_end   = NULL,
  *alloc_ptr            = NULL;

#define isFromSpace(p) ((from_space_ptr<=(p))&&((p)<from_space_ptr_end))

struct cons {
  void *car;
  void *cdr;
};

static int iprintf (const char *fmt, ...)
{
  va_list ap;
  va_start (ap, fmt);
#ifdef DEBUG
  vprintf (fmt, ap);
#endif
  va_end (ap);
}

struct fun {
  void *(*f) (void *, void *, void *);
  void *c;
};

static void *String_compare (void *cl, void *eh, void *vargs)
{
  struct { char *s1, *s2; } *t = untag(vargs,void);
  int res = strcmp (t->s1, t->s2);
  return (void *) boxInt (res);
}

static struct fun compare_fun = { String_compare, NULL };

static void *String_concat (void *cl, void *eh, void *vargs)
{
  void *l;
  size_t len, p;
  char *r;

  for (l = vargs, len = 0; l != NULL; l = untag(l,struct cons)->cdr)
    len += strlen (untag(l,struct cons)->car);
  r = malloc (len + 1);
  if (r == NULL) {
    fputs ("String.concat: cannot allocate\n", stderr);
    exit(1);
  }
  for (l = vargs, p = 0; l != NULL; l = untag(l,struct cons)->cdr) {
    strcpy (r+p, untag(l,struct cons)->car);
    p += strlen (untag(l,struct cons)->car);
  }
  return r;
}

static struct fun concat_fun = { String_concat, NULL };

static void *String_fromInt (void *cl, void *eh, void *vargs)
{
  int i = unboxInt ((int)vargs);
  char *s = malloc (12);
  if (s == NULL) {
    fputs ("String.fromInt: cannot allocate\n", stderr);
    exit (1);
  }
  sprintf (s, "%d", i);
  return s;
}

static struct fun fromInt_fun = { String_fromInt, NULL };

struct dynbuf {
  size_t sz;
  size_t top;
  char *buf;
};

static void init_dynbuf (struct dynbuf *db)
{
  db->sz = db->top = 0;
  db->buf = NULL;
}

static void dyn_push (struct dynbuf *db, char c)
{
  if (db->top >= db->sz) {
    db->sz += BUFSZ;
    db->buf = realloc (db->buf, db->sz);
    if (db->buf == NULL) {
      fputs ("String.inputLine: cannot allocate\n", stderr);
      exit (1);
    }
  }
  db->buf[db->top++] = c;
}

static void *String_inputLine (void *cl, void *eh, void *vargs)
{
  struct dynbuf db;
  int c;

  init_dynbuf (&db);
  while ((c = getchar ()) != EOF) {
    dyn_push (&db, c);
    if (c == '\n')
      break;
  }
  dyn_push (&db, '\0');		
  return db.buf;
}

static struct fun inputLine_fun = { String_inputLine, NULL };

static void *String_output (void *cl, void *eh, void *vargs)
{
  char *s = vargs;
  fputs (s, stdout);
  fflush (stdout);

  return 0;
}

static struct fun output_fun = { String_output, NULL };

static void *String_size (void *cl, void *eh, void *vargs)
{
  char *s = vargs;
  return (void *) boxInt (strlen (s));
}

static struct fun size_fun = { String_size, NULL };

static void *String_sub (void *cl, void *eh, void *vargs)
{
  struct { char *s; int i; } *t = untag(vargs,void);
  return (void *) boxInt ((int) t->s[unboxInt(t->i)]);
}

static struct fun sub_fun = { String_sub, NULL };

static void *String_substring (void *cl, void *eh, void *vargs)
{
  struct { char *s; int start; int len; } *t = untag(vargs,void);
  int len = unboxInt (t->len);
  char *res = malloc (len+1);
  if (res == NULL) {
    fputs ("String.substring: cannot allocate\n", stderr);
    exit (1);
  }
  strncpy (res, t->s + unboxInt (t->start), len);
  res[len+1] = '\0';
  return res;
}

static struct fun substring_fun = { String_substring, NULL };

static void *String_toInt (void *cl, void * eh, void *vargs)
{
  char *s = vargs;
  return (void *) boxInt (atoi (s));
}

static struct fun toInt_fun = { String_toInt, NULL };

void *builtin_mlpr_String[] =
  { NULL,			/* cmdline_args */
    NULL,			/* cmdline_pgm */
    taddr(compare_fun),
    taddr(concat_fun),
    taddr(fromInt_fun),
    taddr(inputLine_fun),
    taddr(output_fun),
    taddr(size_fun),
    taddr(sub_fun),
    taddr(substring_fun),
    taddr(toInt_fun)
  };

/************************************************************************/

void forward(unsigned int *ptr)
{
  unsigned int x = *ptr;

  if (!isInt(x)) {
    // x must be a pointer

    // x-1 because pointer are represented
    // as odd ints.  To make them odd,
    // one is added to their even values,
    // so a 1 must be subtracted to retrieve
    // the original.
    // The outer -1 is adjusts the value to point to the tag
    // (i.e., one word before the base address of the object).
    unsigned int *xp = ((unsigned int *) (x - 1)) - 1;

    if (isFromSpace (xp)) {

      unsigned cur = *xp, new_addr;

      if (isInt(cur)) {		/* cur is a tag value */

	// The tag is actually the exact number of bytes in the record
	// (not including the header word)
	// and, therefore, is naturally divisible by 4.  No tagging is
	// performed on it.
	// + 1 to copy the tag x[-1]
	int n_words = (cur>>2);

	// + 1 because pointers are stored as odd
	// integers.  Since they are already even,
	// adding 1 makes them odd.
	new_addr = (unsigned int) (alloc_ptr + 1) + 1;
	*xp = new_addr;		/* install forwarding pointer */

	// copy (n_words+1) words, i.e., at least one
	do {
	  *alloc_ptr++ = cur;
	  cur = *++xp;
	} while (n_words-- > 0);
      }
      else new_addr = cur;	/* cur is a forwarding pointer */
      *ptr = new_addr;
    }
  }
}

void scan()
{
  unsigned int *scan_ptr = to_space_ptr;
  while (scan_ptr < alloc_ptr) {
    forward(scan_ptr);
    scan_ptr++;
  }
}

void forward_frame_roots(unsigned *start, unsigned *end)
{
  unsigned *cursor;
  for (cursor=start; cursor < end; cursor++)
    forward(cursor);
}

int get_sz_upper(unsigned int raddress)
{
  int i;
  for (i = 0; mlpr_frame_info_table[i] != 0; i = i+3)
    if (mlpr_frame_info_table[i]<= raddress &&
	raddress < mlpr_frame_info_table[i+1])
      return mlpr_frame_info_table[i+2];
  return -1;
}

unsigned mlpr_gc (unsigned amount, unsigned ap, unsigned *limit_ptr,
		  unsigned stack_ptr)
{
  unsigned *cursor = (unsigned *) stack_ptr;
  unsigned *main_sp = mlpr_main_stack_ptr;
  unsigned *previous;
  unsigned raddress;
  unsigned size;
  unsigned sz_upper;

  iprintf("GC!\n");

  alloc_ptr = to_space_ptr;
  limit_ptr = to_space_ptr + HEAPSIZE;

  // handle the GC wrapper frame (not in the table)
  previous = (unsigned *) *cursor;
  size = previous - cursor; 
  sz_upper = 17;
  forward_frame_roots (previous - sz_upper, previous);
  iprintf ("curser = %p, size = %d, sz_upper = %d\n", cursor, size, sz_upper);
  cursor = previous;

  // handle other frames
  while(cursor < main_sp /* && cursor >= (unsigned *)stack_ptr */) {
    previous = (unsigned *) *cursor;
    size = previous - cursor; 
    raddress = *(cursor + 2);
    sz_upper = get_sz_upper (raddress);
    forward_frame_roots (previous - sz_upper, previous);
    iprintf ("curser = %p, size = %d, sz_upper = %d\n", cursor, size, sz_upper);
    cursor = previous;
  }  

  iprintf("scanning...");
  scan();
  iprintf("done\n");

  {
    unsigned *temp = from_space_ptr;
    from_space_ptr = to_space_ptr;
    to_space_ptr = temp;
    from_space_ptr_end = from_space_ptr + HEAPSIZE;
  }

  if(alloc_ptr + amount/4 >= limit_ptr) {
    fputs ("heap exhausted!\n", stderr);
    exit (1);
  }

  mlpr_limit_ptr = limit_ptr;

  iprintf("GC done\n");
  return (unsigned) alloc_ptr;
}

static void *case_blackhole (void *cl, void *eh, void *vp)
{
  fputs ("Black Hole: premature use of `withcases'-constructed value\n",
	 stderr);
  exit (1);
}

static struct fun case_blackhole_fun = { case_blackhole, NULL };

static void *cases_blackhole (void *cl, void *eh, void *vi)
{
  int i = (int)vi;	   // the argument is the actual size in bytes
  // For now we just malloc the blackhole array, the idea being that
  // this does not happen inside of frequently executed code regions.
  // Like the allocation of strings, this needs to be revisited in
  // the future.
  void **a = malloc (i);
  while (i-- > 0)
    a[i] = taddr(case_blackhole_fun);
  return tptr(a);
}

// externally visible; calls to this are inserted by compiler:
struct fun mlpr_cases_blackhole_fun = { cases_blackhole, NULL };

//
// global entry point:
//
int main (int argc, char **argv)
{
  struct cons *arglist;
  int i;

  /**********************************************/

  from_space_ptr = (unsigned int *) malloc (HEAPSIZE*4);
  if (from_space_ptr == NULL) {
    fputs ("cannot obtain from_space\n", stderr);
    return 1;
  }
  from_space_ptr_end = from_space_ptr + HEAPSIZE;

  to_space_ptr = (unsigned int *) malloc (HEAPSIZE*4);
  if (to_space_ptr == NULL) {
    fputs ("cannot obtain to_space\n", stderr);
    return 1;
  }
 /**********************************************/

  if (argc > 1) {
    arglist = malloc ((argc - 1) * sizeof (struct cons));
    if (arglist == NULL) {
      fputs ("cannot allocate argument list\n", stderr);
      return 1;
    }

    for (i = 1; i < argc; i++) {
      arglist[i-1].car = argv[i];
      arglist[i-1].cdr = taddr(arglist[i]);
    }
    arglist[argc-2].cdr = NULL;
  }
  else
    arglist = NULL;

  builtin_mlpr_String[1] = argv[0];
  builtin_mlpr_String[0] = arglist == NULL ? NULL : taddr(arglist[0]);

  return unboxInt (mlpr_entrypoint (builtin_mlpr_String[1],
				    builtin_mlpr_String[0],
				    from_space_ptr,
				    from_space_ptr_end));
}

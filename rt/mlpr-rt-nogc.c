# include <stdio.h>
# include <stdlib.h>
# include <string.h>

# define HEAPSIZE (1024*1024)	/* one megabyte */

# define BUFSZ 128

extern int mlpr_entrypoint (void *, void *, void *, void *);

#define taddr(x) ((void*)(((char *)(void *)&(x))+1))
#define untag(x,t) ((t*)(((char*)(void*)(x))-1))

#define boxInt(i) ((i)<<1)
#define unboxInt(i) ((i)>>1)

struct cons {
  void *car;
  void *cdr;
};

int main (int argc, char **argv)
{
  char *heap, *limit;
  struct cons *arglist;
  int i;

  heap = malloc (HEAPSIZE);
  if (heap == NULL) {
    fputs ("cannot obtain heap\n", stderr);
    return 1;
  }
  limit = heap + HEAPSIZE;
  
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

  return mlpr_entrypoint (argv[0], (arglist == NULL) ? NULL : taddr(arglist[0]), heap, limit);
}

struct fun {
  void *(*f) (void *, void *);
  void *c;
};

static void *String_compare (void *cl, void *vp)
{
  char **p = untag(vp,char*);
  int res = strcmp (p[0], p[1]);
  return (void *) boxInt (res);
}

static struct fun compare_fun = { String_compare, NULL };

static void *String_concat (void *cl, void *vl)
{
  void *l;
  size_t len, p;
  char *r;
  

  for (l = vl, len = 0; l != NULL; l = untag(l,struct cons)->cdr)
    len += strlen (untag(l,struct cons)->car);
  r = malloc (len + 1);
  if (r == NULL) {
    fputs ("String.concat: cannot allocate\n", stderr);
    exit(1);
  }
  for (l = vl, p = 0; l != NULL; l = untag(l,struct cons)->cdr) {
    strcpy (r+p, untag(l,struct cons)->car);
    p += strlen (untag(l,struct cons)->car);
  }
  return r;
}

static struct fun concat_fun = { String_concat, NULL };

static void *String_fromInt (void *cl, void *vi)
{
  int i = unboxInt ((int)vi);
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

static void *String_inputLine (void *cl, void *vs)
{
  struct dynbuf db;
  int c;

  init_dynbuf (&db);
  while ((c = getchar ()) != EOF) {
    dyn_push (&db, c);
    if (c == '\n')
      break;
  }
  dyn_push (&db, '\0');		/* this guarantees that result won't be NULL */
  return db.buf;
}

static struct fun inputLine_fun = { String_inputLine, NULL };

static void *String_output (void *cl, void *vs)
{
  char *s = vs;
  fputs (s, stdout);
  fflush (stdout);
  return 0;
}

static struct fun output_fun = { String_output, NULL };

static void *String_size (void *cl, void *vs)
{
  char *s = vs;
  return (void *) boxInt (strlen (s));
}

static struct fun size_fun = { String_size, NULL };

static void *String_sub (void *cl, void *vp)
{
  struct { char *s; int i; } *p = untag(vp,void);
  return (void *) boxInt ((int) p->s[unboxInt(p->i)]);
}

static struct fun sub_fun = { String_sub, NULL };

static void *String_substring (void *cl, void *vt)
{
  struct { char *s; int start; int len; } *t = untag(vt,void);
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

static void *String_toInt (void *cl, void *vs)
{
  return (void *) boxInt (atoi ((char *)vs));
}

static struct fun toInt_fun = { String_toInt, NULL };

struct fun *builtin_mlpr_String[] =
  { taddr(compare_fun),
    taddr(concat_fun),
    taddr(fromInt_fun),
    taddr(inputLine_fun),
    taddr(output_fun),
    taddr(size_fun),
    taddr(sub_fun),
    taddr(substring_fun),
    taddr(toInt_fun)
  };

void mlpr_gc (void)
{
  fputs ("heap exhausted!\n", stderr);
  exit (1);
}

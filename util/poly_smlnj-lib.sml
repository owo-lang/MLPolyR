structure Word31 = Word;
structure Int32 = Int;
structure Unsafe = struct
          structure CharVector = CharVector
          structure Array = Array
          structure Word8Array = Word8Array
      end;
local

val util = [
"ord-key-sig.sml",
"ord-set-sig.sml",
"lib-base-sig.sml",
"lib-base.sml",
"list-set-fn.sml",
"ord-map-sig.sml",
"list-map-fn.sml",
"int-binary-set.sml",
"int-binary-map.sml",
"prime-sizes.sml",
"dynamic-array-sig.sml",
"dynamic-array.sml",
"io-util-sig.sml",
"splaytree-sig.sml",
"splaytree.sml",
"splay-set-fn.sml",
"splay-map-fn.sml",
"ansi-term.sml",
"io-util.sml",
"plist-sig.sml",
"getopt-sig.sml",
"getopt.sml",
"interval-domain-sig.sml",
"interval-set-sig.sml",
"parser-comb-sig.sml",
"atom-sig.sml",
"hash-string.sml",
"atom.sml",
"format-sig.sml",
"real-format.sml",
"fmt-fields.sml",
"format.sml",
"priority-sig.sml",
"hash-key-sig.sml",
"mono-hash-table-sig.sml",
"hash-table-rep.sml",
"int-hash-table.sml",
"redblack-set-fn.sml",
"atom-redblack-set.sml",
"atom-set.sml",
"redblack-map-fn.sml",
"atom-redblack-map.sml",
"atom-map.sml",
"plist.sml",
"char-map-sig.sml",
"char-map.sml",
"list-xprod-sig.sml",
"graph-scc-sig.sml",
"graph-scc-fn.sml",
"hash-table-fn.sml",
"atom-table.sml",
"list-format-sig.sml",
"list-format.sml",
"parser-comb.sml",
"mono-hash2-table-sig.sml",
"interval-set-fn.sml",
"word-redblack-set.sml",
"word-redblack-map.sml",
"int-list-set.sml",
"int-list-map.sml",
"path-util-sig.sml",
"path-util.sml",
"binary-set-fn.sml",
"binary-map-fn.sml",
"random-sig.sml",
"random.sml",
"real-order-stats.sml",
"univariate-stats.sml",
"mono-array-fn.sml",
"bsearch-fn.sml",
"mono-dynamic-array-sig.sml",
"format-comb-sig.sml",
"format-comb.sml",
"queue-sig.sml",
"fifo-sig.sml",
"fifo.sml",
"queue.sml",
"hash2-table-fn.sml",
"word-hash-table.sml",
"keyword-fn.sml",
"mono-priorityq-sig.sml",
"left-priorityq-fn.sml",
"hash-table-sig.sml",
"hash-table.sml",
"dynamic-array-fn.sml",
"mono-array-sort-sig.sml",
"int-redblack-set.sml",
"int-redblack-map.sml",
"array-sort-sig.sml",
"array-qsort.sml",
"uref-sig.sml",
"simple-uref.sml",
"listsort-sig.sml",
"list-mergesort.sml",
"array-qsort-fn.sml",
"atom-binary-set.sml",
"atom-binary-map.sml",
"utf8-sig.sml",
"utf8.sml",
"uref.sml",
"scan-sig.sml",
"scan.sml",
"rand-sig.sml",
"rand.sml",
"list-xprod.sml",
""]


fun dol ("",_) =()
  | dol (dn,l) =List.app(fn "" => ()
                                | s => use("util/smlnj-lib/"^s)) l
in
val _ = List.app dol [
("Util", util),
("", [])]
end;
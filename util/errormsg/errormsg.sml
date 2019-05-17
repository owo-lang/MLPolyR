(* This file is a stub, needs rewrite *)
signature ERRORMSG =
sig
    val anyErrors : bool ref
    val fileName : string ref
    val lineNum : int ref
    val linePos : int list ref
    val sourceStream : TextIO.instream ref
    val error : int * int -> string -> unit
    exception Error
    val impossible : string -> 'a   (* raises Error *)
    val matchErrorString : Source.inputSource -> SourceMap.region -> string
    val reset : unit -> unit
end

structure ErrorMsg : ERRORMSG =
struct

  val anyErrors = ref false
  val fileName = ref ""
  val lineNum = ref 1
  val linePos = ref [1]
  val sourceStream = ref TextIO.stdIn

  fun reset() = (anyErrors:=false;
		 fileName:="";
		 lineNum:=1;
		 linePos:=[1];
		 sourceStream:=TextIO.stdIn)

  exception Error

  fun error (x,y) (msg:string) =
      (app print [":",
				          Int.toString x,
				          ".",
				          Int.toString y];
	     print ":";
	     print msg;
	     print "\n")


  fun impossible msg =
      (app print ["Error: Compiler bug: ",msg,"\n"];
       TextIO.flushOut TextIO.stdOut;
       raise Error)

  fun location_string ({sourceMap,fileOpened,...}:Source.inputSource)
                      ((p1,p2): SourceMap.region) : string =
      let fun shortpoint ({line, column,...}:SourceMap.sourceloc, l) = 
              Int.toString line :: "." :: Int.toString column :: l
          fun showpoint (p as {fileName,...}:SourceMap.sourceloc, l) = 
              fileName :: ":" :: shortpoint (p, l)
          fun allfiles(f, (src:SourceMap.sourceloc, _)::l) = 
              f = #fileName src andalso allfiles(f, l)
            | allfiles(f, []) = true
          fun lastpos [(_, hi)] = hi
            | lastpos (h::t) = lastpos t
            | lastpos [] = impossible "lastpos botch in ErrorMsg.location_string"
      in  concat (
              case SourceMap.fileregion sourceMap (p1, p2)
               of [(lo, hi)] => 
                  if p1+1 >= p2 then showpoint (lo, [])
                  else showpoint(lo, "-" :: shortpoint(hi, []))
                | (lo, _) :: rest =>
                  if allfiles(#fileName lo, rest) then
                      showpoint(lo, "..." :: shortpoint(lastpos rest, []))
                  else
                      showpoint(lo, "..." :: showpoint (lastpos rest, []))
                | [] => [fileOpened, ":<nullRegion>"]
          )
      end

  val matchErrorString = location_string

end  (* structure ErrorMsg *)
  

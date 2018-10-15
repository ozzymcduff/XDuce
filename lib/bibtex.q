(* Bibtex interface for XDuce
   Based on a bibtex (0.99b) document "BibTeXing" by Oren Patashnik
*)

(* The external bibtex parser returns a tree (roughly) of type Biblio0
*)

type Key = key[String]
type AnyFs = ~[String*]*

type Biblio0 = 
    ~@(Key)[AnyFs]*

extern load_bib0 : String -> Biblio0

(* Finer types for each bib entry.  Since XDuce doesn't handle
   unordered record types, we imitate them by ordered sequence types
   where the fields are alphabetically sorted and AnyFs type is
   inserted before, after, and between fields.  Only required fields
   are included since optional fields do not make types change.  *)

type Article = 
   article@(Key)[AnyFs, Author, AnyFs, Journal, AnyFs, Title, AnyFs, Year, AnyFs]

type Book = 
   book@(Key)[AnyFs, (Author | Editor), AnyFs, Publisher, AnyFs, Title, AnyFs, Year, AnyFs]

type Booklet = 
   booklet@(Key)[AnyFs, Title, AnyFs]

subtag conference <: inproceedings

(* skipped Inbook... *)

type Incollection = 
   incollection@(Key)[AnyFs, Author, AnyFs, Booktitle, AnyFs, Publisher, AnyFs, Title, AnyFs, Year, AnyFs]
   
type Inproceedings =
   inproceedings@(Key)[AnyFs, Author, AnyFs, Booktitle, AnyFs, Title, AnyFs, Year, AnyFs]

type Misc = 
   misc@(Key)[AnyFs]

type Manual = 
   manual@(Key)[AnyFs, Title, AnyFs]

type Mastersthesis =
   mastersthesis@(Key)[AnyFs, Author, AnyFs, School, AnyFs, Title, AnyFs, Year, AnyFs]

type Phdthesis =
   phdthesis@(Key)[AnyFs, Author, AnyFs, School, AnyFs, Title, AnyFs, Year, AnyFs]

type Proceedings =
   proceedings@(Key)[AnyFs, Title, AnyFs, Year, AnyFs]

type Techreport =
   techreport@(Key)[AnyFs, Author, AnyFs, Institution, AnyFs, Title, AnyFs, Year, AnyFs]

type Unpublished =
   unpublished@(Key)[AnyFs, Author, AnyFs, Note, AnyFs, Title, AnyFs]

type Author = author[String]
type Journal = journal[String]
type Title = title[String]
type Year = year[String]
type Editor = editor[String]
type Publisher = publisher[String]
type Booktitle = booktitle[String]
type School = school[String]
type Institution = institution[String]
type Note = note[String]

type BibEntry =
    Article | Book | Booklet | Incollection | Inproceedings | Misc | 
    Manual | Mastersthesis | Phdthesis | Proceedings | 
    Techreport | Unpublished

type Biblio = BibEntry*

fun load_bib (val fname as String) : Biblio =
  validate load_bib0(fname) with Biblio
   
   

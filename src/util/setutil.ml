module MakePair(O1 : Set.OrderedType)(O2 : Set.OrderedType) 
  : (Set.OrderedType with type t = O1.t * O2.t) =
  struct 
    type t = O1.t * O2.t
    let compare (x1, y1 : t) (x2, y2 : t) =
      let c = O1.compare x1 x2 in
      if c <> 0 then c else
      let c = O2.compare y1 y2 in
      c
  end

module MakeTuple3(O1 : Set.OrderedType)(O2 : Set.OrderedType)(O3 : Set.OrderedType) 
  : (Set.OrderedType with type t = O1.t * O2.t * O3.t) =
  struct 
    type t = O1.t * O2.t * O3.t
    let compare (x1, y1, z1 : t) (x2, y2, z2 : t) =
      let c = O1.compare x1 x2 in
      if c <> 0 then c else
      let c = O2.compare y1 y2 in
      if c <> 0 then c else
      let c = O3.compare z1 z2 in
      c
  end

module MakeTuple4(O1 : Set.OrderedType)(O2 : Set.OrderedType)(O3 : Set.OrderedType)(O4 : Set.OrderedType) 
  : (Set.OrderedType with type t = O1.t * O2.t * O3.t * O4.t) =
  struct 
    type t = O1.t * O2.t * O3.t * O4.t
    let compare (w1, x1, y1, z1 : t) (w2, x2, y2, z2 : t) =
      let c = O1.compare w1 w2 in
      if c <> 0 then c else
      let c = O2.compare x1 x2 in
      if c <> 0 then c else
      let c = O3.compare y1 y2 in
      if c <> 0 then c else
      let c = O4.compare z1 z2 in
      c
  end

module MakeTuple5(O1 : Set.OrderedType)(O2 : Set.OrderedType)(O3 : Set.OrderedType)(O4 : Set.OrderedType)(O5 : Set.OrderedType)  
  : (Set.OrderedType with type t = O1.t * O2.t * O3.t * O4.t * O5.t) =
  struct 
    type t = O1.t * O2.t * O3.t * O4.t * O5.t
    let compare (v1, w1, x1, y1, z1 : t) (v2, w2, x2, y2, z2 : t) =
      let c = O1.compare v1 v2 in
      if c <> 0 then c else
      let c = O2.compare w1 w2 in
      if c <> 0 then c else
      let c = O3.compare x1 x2 in
      if c <> 0 then c else
      let c = O4.compare y1 y2 in
      if c <> 0 then c else
      let c = O5.compare z1 z2 in
      c
  end

module MakeSortedlist(O1 : Set.OrderedType)
  : (Set.OrderedType with type t = O1.t list) =
  struct
    type t = O1.t list
    let compare x y = Sortedlist.compare O1.compare x y
  end

module String =
  struct
    type t = string
    let compare = compare
  end

module Bool =
  struct
    type t = bool
    let compare = compare
  end

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)


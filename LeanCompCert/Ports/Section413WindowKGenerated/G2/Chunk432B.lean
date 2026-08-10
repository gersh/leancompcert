import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432A

def state06 : KState := ⟨⟨360584688980333741, 360584700581746329⟩, ⟨(-68521121698459844), (-68181953260958268)⟩, true⟩

def words05 : List Nat := [360583123436343465, 360583123796482316, 360583123982919082, 360583124460119349, 360583124673570030, 360583124887106919, 360583124887632479, 360583124831770251, 360583124484130573, 360583124521247012]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564171483255822, 360564183090222290⟩, ⟨819183835121515531, 819523243848025181⟩, true⟩

def words06 : List Nat := [360583125092310956, 360583125321658575, 360583125322194488, 360583125087668529, 360583124853055722, 360583124305027309, 360583124024763882, 360583123721673290, 360583123418531764, 360583122846262226]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360633854693549415, 360633866306083970⟩, ⟨(-2196337338434453943), (-2195997688749134533)⟩, true⟩

def words07 : List Nat := [360583122505292770, 360583122602198670, 360583123118146791, 360583123915032203, 360583124246689807, 360583124578378043, 360583125062554979, 360583125814486555, 360583126987341149, 360583128160275206]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360642904228173496, 360642915846344348⟩, ⟨(-2588195195616873319), (-2587855301966252501)⟩, true⟩

def words08 : List Nat := [360583128904568790, 360583129773339028, 360583131175545146, 360583132577859444, 360583133630219568, 360583134443151228, 360583134945076081, 360583135447052313, 360583136328406647, 360583137709965742]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588928998970673, 360588940622696224⟩, ⟨(-251183631532382167), (-250843497390298153)⟩, true⟩

def words09 : List Nat := [360583139624687637, 360583141539434242, 360583143185103223, 360583144299220245, 360583145049059119, 360583145799015728, 360583146832917787, 360583147335393202, 360583147469719665, 360583147604119510]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432B

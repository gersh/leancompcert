import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546741042214861, 360546756465598077⟩, ⟨1741567278098383343, 1742084198279494015⟩, true⟩

def state01 : KState := ⟨⟨360599631565388036, 360599646995239583⟩, ⟨(-881993981520511375), (-881476740478665841)⟩, true⟩

def words00 : List Nat := [360581878423335068, 360581878039068978, 360581878301690672, 360581878635986292, 360581878636616994, 360581878620742279, 360581878652960450, 360581878832632265, 360581878868332435, 360581879227194620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583922032532066, 360583937468888093⟩, ⟨(-102502741826492600), (-101985178064382574)⟩, true⟩

def words01 : List Nat := [360581879325131818, 360581879423139126, 360581879926062236, 360581880634059200, 360581881241413874, 360581881848867535, 360581882178087793, 360581882178772114, 360581882144084013, 360581882186284672]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573394167811596, 360573409610623275⟩, ⟨419769829217977575, 420287713341723417⟩, true⟩

def words02 : List Nat := [360581882186844311, 360581882085005079, 360581881737635294, 360581881030182607, 360581880322647488, 360581879502991187, 360581878892248524, 360581878686491927, 360581878480667522, 360581878031202395]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360622018938125457, 360622034387395856⟩, ⟨(-1993737102384391361), (-1993218897682082237)⟩, true⟩

def words03 : List Nat := [360581877935409678, 360581878010447114, 360581878490019245, 360581879050683707, 360581879269809423, 360581879488973927, 360581879689171983, 360581880094190324, 360581880903653812, 360581881713241789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593635667483156, 360593651123272417⟩, ⟨(-584849724726407151), (-584331196395819019)⟩, true⟩

def words04 : List Nat := [360581882320214693, 360581882522345342, 360581882786450694, 360581883050762521, 360581883214614595, 360581883215299350, 360581883090173211, 360581882661124613, 360581882231961574, 360581882353330305]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564453321666548, 360564468783913585⟩, ⟨864202740862304197, 864721589854062809⟩, true⟩

def words05 : List Nat := [360581882454260466, 360581882555307916, 360581882555924260, 360581882458007013, 360581882458580188, 360581882369764528, 360581882280754030, 360581882120775442, 360581881972952425, 360581881623016567]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625332539500662, 360625348008208945⟩, ⟨(-2159370531398481044), (-2158851361509438412)⟩, true⟩

def words06 : List Nat := [360581881272936457, 360581881366491025, 360581881938198065, 360581882510013327, 360581882647983446, 360581882648670127, 360581882979122857, 360581883346895878, 360581884118602770, 360581884994347549]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598915721672619, 360598931196922885⟩, ⟨(-847045590102136139), (-846526095240794067)⟩, true⟩

def words07 : List Nat := [360581885665739910, 360581886337186261, 360581887128963006, 360581888200526266, 360581889162055734, 360581890123662215, 360581890828585922, 360581891277388901, 360581891620946378, 360581891964716593]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593598613005511, 360593614094707720⟩, ⟨(-582873126155356854), (-582353310728620818)⟩, true⟩

def words08 : List Nat := [360581892712217794, 360581893055645747, 360581893196856424, 360581893338136302, 360581893338711206, 360581893559193102, 360581893895879451, 360581894232679786, 360581894365466720, 360581894602028390]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589740158165834, 360589755646349456⟩, ⟨(-391280717949533789), (-390760580430332429)⟩, true⟩

def words09 : List Nat := [360581894786610795, 360581894971385247, 360581895041165781, 360581895041851398, 360581894707712257, 360581894024960042, 360581893342104074, 360581893100945270, 360581893259702420, 360581893418619022]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496

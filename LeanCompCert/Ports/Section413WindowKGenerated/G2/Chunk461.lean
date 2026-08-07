import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk461

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583388570264129, 360583401813951430⟩, ⟨(-9362065961099651), (-8949493920872469)⟩, true⟩

def state01 : KState := ⟨⟨360574735175131864, 360574748424844411⟩, ⟨389556585571758562, 389969435405040738⟩, true⟩

def words00 : List Nat := [360583207686540355, 360583207328491286, 360583207417349178, 360583207696899431, 360583207857439852, 360583207858072225, 360583207549102485, 360583206972094232, 360583206394998967, 360583205797115178]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360518659636693469, 360518672892361919⟩, ⟨2975531474191060541, 2975944598680918835⟩, true⟩

def words01 : List Nat := [360583205614215584, 360583205569302935, 360583205524320117, 360583205187514331, 360583204381224361, 360583203324439860, 360583202267496594, 360583201573256321, 360583200409621302, 360583199011153787]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360532314154429436, 360532327416076170⟩, ⟨2345601142503231620, 2346014542741064856⟩, true⟩

def words02 : List Nat := [360583197612605060, 360583196373022587, 360583195369340125, 360583194111483385, 360583192853635169, 360583191164423214, 360583189005960240, 360583187216794815, 360583185427521127, 360583184007074243]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541135312374282, 360541148580046637⟩, ⟨1938676724646942461, 1939090402875735605⟩, true⟩

def words03 : List Nat := [360583182905199329, 360583181568684273, 360583180232104694, 360583179364463589, 360583178859762575, 360583178236582234, 360583177613372082, 360583176609335293, 360583175723452194, 360583174813312258]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551118713473149, 360551131987101311⟩, ⟨1477914147709807493, 1478328100769801961⟩, true⟩

def words04 : List Nat := [360583173903002051, 360583173461396097, 360583172550761430, 360583171405630152, 360583170260437908, 360583168805372130, 360583167585862564, 360583166834984786, 360583166084070321, 360583165098710625]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576273124369188, 360576286403979673⟩, ⟨316772505620775610, 317186734794122048⟩, true⟩

def words05 : List Nat := [360583164405138835, 360583163537004595, 360583162668716124, 360583162268944496, 360583161560319280, 360583160406716535, 360583159253038411, 360583158443380376, 360583158015248225, 360583157867038472]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360528755175391816, 360528768461035080⟩, ⟨2510201065913973801, 2510615573589062843⟩, true⟩

def words06 : List Nat := [360583157718749877, 360583157249549608, 360583156311702527, 360583155335337883, 360583154358857224, 360583153060875188, 360583151503464028, 360583149583868115, 360583147664233629, 360583146099622671]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360507447347521607, 360507460639137268⟩, ⟨3494179054025831313, 3494593837476680015⟩, true⟩

def words07 : List Nat := [360583144922390346, 360583144213331178, 360583143504220895, 360583142560954721, 360583141149320639, 360583139615233984, 360583138081024763, 360583136872243834, 360583135595442158, 360583133957402246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560714447645226, 360560727745239391⟩, ⟨1034179535094494144, 1034594594662368180⟩, true⟩

def words08 : List Nat := [360583132319289906, 360583131149205056, 360583130259716075, 360583129838138287, 360583129416528461, 360583128595454781, 360583127791879154, 360583127456232839, 360583127120417465, 360583126415831779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360538110800179808, 360538124103813003⟩, ⟨2078324369899577186, 2078739708439752594⟩, true⟩

def words09 : List Nat := [360583125931482080, 360583125181999018, 360583124432436011, 360583123671503354, 360583123145592990, 360583122501275007, 360583121856922080, 360583120883900805, 360583119442981083, 360583118469796548]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk461

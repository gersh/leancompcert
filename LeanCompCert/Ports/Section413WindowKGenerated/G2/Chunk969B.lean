import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969A

def state06 : KState := ⟨⟨360594911299853729, 360594973454535622⟩, ⟨(-1225914524158989797), (-1221845172695501723)⟩, true⟩

def words05 : List Nat := [360582370744177118, 360582370795128480, 360582370952218301, 360582371195583014, 360582371411413740, 360582371627469649, 360582371758348973, 360582371783327912, 360582371914432994, 360582372046003372]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582797943291952, 360582860111223906⟩, ⟨(-51360791459098481), (-47290155202229397)⟩, true⟩

def words06 : List Nat := [360582372249357837, 360582372346968570, 360582372390944218, 360582372435097193, 360582372436283804, 360582372385339040, 360582372418442382, 360582372451816322, 360582372453070004, 360582372438051492]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597836746660444, 360597898927896587⟩, ⟨(-1509818495417047588), (-1505746568987420228)⟩, true⟩

def words07 : List Nat := [360582372440057777, 360582372442457108, 360582372550801867, 360582372553430727, 360582372554742336, 360582372465904743, 360582372376785963, 360582372403378041, 360582372564615888, 360582372726176793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585641949587055, 360585704144212816⟩, ⟨(-327205903272159460), (-323132678250102692)⟩, true⟩

def words08 : List Nat := [360582372834078730, 360582372836158897, 360582372927231621, 360582373018731849, 360582373019933595, 360582373011001257, 360582372925444013, 360582372760216777, 360582372594723168, 360582372570373490]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569316458625669, 360569378666526364⟩, ⟨1256296837518573759, 1260371350142082897⟩, true⟩

def words09 : List Nat := [360582372656091269, 360582372742100105, 360582372759810515, 360582372761218179, 360582372672892548, 360582372535334518, 360582372397365527, 360582372365985258, 360582372318095867, 360582372185599994]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969B

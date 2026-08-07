import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587084789505972, 360587146864310976⟩, ⟨(-467492824430730098), (-463431215431027122)⟩, true⟩

def state01 : KState := ⟨⟨360589806361322487, 360589868449382500⟩, ⟨(-731299853546430953), (-727236960069604831)⟩, true⟩

def words00 : List Nat := [360582364372136297, 360582364373549139, 360582364372447715, 360582364294319877, 360582364215964223, 360582364110804057, 360582364126623437, 360582364188652250, 360582364196961633, 360582364275861748]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607295417130421, 360607357518453986⟩, ⟨(-2426245879442506497), (-2422181700528697801)⟩, true⟩

def words01 : List Nat := [360582364460937915, 360582364646437909, 360582364923629532, 360582365128952001, 360582365236765960, 360582365344658056, 360582365488435884, 360582365701038681, 360582365960038258, 360582366219349265]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600386640399748, 360600448755148219⟩, ⟨(-1756629818216223945), (-1752564338097150655)⟩, true⟩

def words02 : List Nat := [360582366395549608, 360582366621702263, 360582366929458505, 360582367237622185, 360582367518562812, 360582367693643401, 360582367815053571, 360582367936621566, 360582368031995002, 360582368220148094]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590485699752032, 360590547827742125⟩, ⟨(-796825730759898695), (-792758967063598747)⟩, true⟩

def words03 : List Nat := [360582368514270841, 360582368808666756, 360582369043694390, 360582369242391536, 360582369413684448, 360582369585373951, 360582369770436974, 360582369909350738, 360582369994976296, 360582370080792294]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594272274883047, 360594334416169068⟩, ⟨(-1163962941285418915), (-1159894888617261549)⟩, true⟩

def words04 : List Nat := [360582370197482321, 360582370375591750, 360582370498291102, 360582370621230161, 360582370646103526, 360582370647510461, 360582370566184285, 360582370542548914, 360582370568490206, 360582370693374902]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969

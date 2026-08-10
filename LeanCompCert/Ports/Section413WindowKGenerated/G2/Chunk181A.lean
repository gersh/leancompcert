import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk181A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360490653057156911, 360490654941643787⟩, ⟨1691529884954917746, 1691552972763200932⟩, true⟩

def state01 : KState := ⟨⟨360544631458556777, 360544633345219811⟩, ⟨714524252844928346, 714547380052394802⟩, true⟩

def words00 : List Nat := [360584105744148562, 360584101935957470, 360584100900864975, 360584101287626290, 360584101287838946, 360584098685856239, 360584095699362232, 360584093982431796, 360584092265625790, 360584089302152578]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360519220717264564, 360519222606118087⟩, ⟨1174860105476265160, 1174883272364624906⟩, true⟩

def words01 : List Nat := [360584087123794603, 360584083412384594, 360584079701340540, 360584077874077729, 360584077574078528, 360584076498437511, 360584075422889598, 360584071832098645, 360584065217057622, 360584061638809292]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360635766845640766, 360635768736669011⟩, ⟨(-937596501839614836), (-937573295534822996)⟩, true⟩

def words02 : List Nat := [360584058060880204, 360584058136241014, 360584058136449732, 360584056411886148, 360584054687475429, 360584051633364615, 360584052475196370, 360584054413197459, 360584054820511571, 360584057672991618]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360646558374596276, 360646560267798459⟩, ⟨(-1133007579437703152), (-1132984333708355542)⟩, true⟩

def words03 : List Nat := [360584063558045891, 360584069442518129, 360584078358885699, 360584084253800500, 360584087622871572, 360584090991586239, 360584094251794341, 360584099032810151, 360584102476285999, 360584105919432418]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360655021447887714, 360655023343287040⟩, ⟨(-1287059059763616142), (-1287035774167447386)⟩, true⟩

def words04 : List Nat := [360584107833685252, 360584107914187733, 360584111023984586, 360584114133512633, 360584115713901133, 360584115714131955, 360584115580068657, 360584113470873112, 360584112281084780, 360584116188079755]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk181A

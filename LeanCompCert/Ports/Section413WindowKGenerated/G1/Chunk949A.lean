import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487579470405269, 362487716307700170⟩, ⟨(-248086726453458499), (-239319140412011163)⟩, true⟩

def state01 : KState := ⟨⟨362504167203500810, 362504304070525496⟩, ⟨(-1822325263144076809), (-1813554855590523973)⟩, true⟩

def words00 : List Nat := [371285194650837861, 371285194716848498, 371285194892566244, 371285195069664410, 371285195225247777, 371285195289366627, 371285195463468333, 371285195639282862, 371285195913509360, 371285196118279808]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492075338405443, 362492212235811100⟩, ⟨(-674613177221470500), (-665839886060368298)⟩, true⟩

def words01 : List Nat := [371285196308555692, 371285196499992723, 371285196711602600, 371285196869008415, 371285197043191833, 371285197218616128, 371285197386553162, 371285197407351433, 371285197483524425, 371285197561649847]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486393270657350, 362486530197681513⟩, ⟨(-135232921956275758), (-126456819251919370)⟩, true⟩

def words02 : List Nat := [371285197717503186, 371285197749022238, 371285197781319793, 371285197814694601, 371285197880893668, 371285197906139878, 371285197966449238, 371285198028126114, 371285198088249054, 371285198105748932]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505624417671648, 362505761374690425⟩, ⟨(-1960924431354297180), (-1952145481106952274)⟩, true⟩

def words03 : List Nat := [371285198213595258, 371285198323170166, 371285198542061756, 371285198669895614, 371285198780102313, 371285198891373072, 371285199105568603, 371285199265879568, 371285199484726544, 371285199705010235]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494866744384617, 362495003731496879⟩, ⟨(-939593532653458184), (-930811725181773714)⟩, true⟩

def words04 : List Nat := [371285199887175676, 371285199941660054, 371285200072677828, 371285200205470619, 371285200347886695, 371285200371334226, 371285200393551559, 371285200416925465, 371285200549933378, 371285200657014444]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949A

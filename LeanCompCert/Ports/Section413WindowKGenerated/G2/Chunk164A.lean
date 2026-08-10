import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668782917229547, 360668784450430925⟩, ⟨(-1411739720191880489), (-1411722697386160939)⟩, true⟩

def state01 : KState := ⟨⟨360620821172859694, 360620822708031415⟩, ⟨(-625536758026564569), (-625519702897453777)⟩, true⟩

def words00 : List Nat := [360582710693492183, 360582710693698912, 360582712035750913, 360582713863539754, 360582713863713341, 360582713448183988, 360582712023211613, 360582708728004891, 360582705433157027, 360582706828261904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360535499257315232, 360535500794433983⟩, ⟨775389175800476269, 775406262890289257⟩, true⟩

def words01 : List Nat := [360582712854122795, 360582718879290152, 360582723030027702, 360582725313274260, 360582725313450471, 360582724790606732, 360582727445477838, 360582727445684704, 360582726950678363, 360582724074756169]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360665728504263432, 360665730043337765⟩, ⟨(-1363430844752125626), (-1363413725542212678)⟩, true⟩

def words02 : List Nat := [360582722023325609, 360582726290225085, 360582731075550039, 360582735860330678, 360582737507197695, 360582737507404769, 360582740396462672, 360582743689239144, 360582746858367351, 360582751908985492]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360640304298770579, 360640305839816484⟩, ⟨(-945372950589978446), (-945355798977301644)⟩, true⟩

def words03 : List Nat := [360582755089079647, 360582758268810369, 360582765142092581, 360582774847976393, 360582782724006109, 360582790599114396, 360582796605470944, 360582798947328074, 360582802445482344, 360582805943278725]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608022899456644, 360608024442456587⟩, ⟨(-414903852426403131), (-414886668679730865)⟩, true⟩

def words04 : List Nat := [360582811496503461, 360582813386183407, 360582813386373147, 360582812156404892, 360582810926554738, 360582806102806328, 360582803823397825, 360582804527408733, 360582804527593449, 360582804901475508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164A

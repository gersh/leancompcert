import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582511746742825, 360582572761627666⟩, ⟨(-33572203555763478), (-29612877424467128)⟩, true⟩

def state01 : KState := ⟨⟨360588778648017814, 360588839676077645⟩, ⟨(-635867623364217373), (-631907031051359431)⟩, true⟩

def words00 : List Nat := [360582264659215963, 360582264765757527, 360582264869295148, 360582264973078830, 360582264977904026, 360582264979299099, 360582264925180947, 360582264887903166, 360582264850222079, 360582264913240391]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596359526386595, 360596420567724057⟩, ⟨(-1364536844144754128), (-1360574975654916578)⟩, true⟩

def words01 : List Nat := [360582264917232011, 360582264921363923, 360582265011532055, 360582265161503724, 360582265268186273, 360582265375093849, 360582265396171783, 360582265455431798, 360582265603823540, 360582265752692432]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598690174044233, 360598751228503806⟩, ⟨(-1588576284108413538), (-1584613154254241092)⟩, true⟩

def words02 : List Nat := [360582265948732490, 360582266113055430, 360582266221184008, 360582266329487014, 360582266408457184, 360582266558627166, 360582266787457391, 360582267016550219, 360582267162208115, 360582267335126496]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360614434010521187, 360614495078169175⟩, ⟨(-3102189210287713134), (-3098224812569994324)⟩, true⟩

def words03 : List Nat := [360582267482025108, 360582267629309768, 360582267865349219, 360582268023656174, 360582268083386359, 360582268143213452, 360582268310990774, 360582268561758877, 360582268898090010, 360582269234745766]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603651585302524, 360603712666212195⟩, ⟨(-2065607445384683559), (-2061641772623275827)⟩, true⟩

def words04 : List Nat := [360582269511998269, 360582269715910869, 360582270000667241, 360582270285827341, 360582270472605854, 360582270551728974, 360582270575919160, 360582270600255456, 360582270732506646, 360582270957102324]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961A

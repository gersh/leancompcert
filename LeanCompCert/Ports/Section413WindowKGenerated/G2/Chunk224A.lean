import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603046674334915, 360603049616112072⟩, ⟨(-511828145395579631), (-511783560456437171)⟩, true⟩

def state01 : KState := ⟨⟨360593055028682775, 360593057973221302⟩, ⟨(-288346742910407353), (-288302096103120083)⟩, true⟩

def words00 : List Nat := [360580203155926975, 360580202895595147, 360580201825706004, 360580201892873527, 360580201893116229, 360580201449200080, 360580200368008831, 360580197278256910, 360580194188725463, 360580193661227053]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577887579702229, 360577890526971803⟩, ⟨51788835011190721, 51833543035025251⟩, true⟩

def words01 : List Nat := [360580195613624451, 360580197565904266, 360580198386549779, 360580199269541584, 360580199642675334, 360580200015852276, 360580201425157713, 360580202562764589, 360580202563025635, 360580202460202625]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579011879263174, 360579014829276212⟩, ⟨26605002752794576, 26649772298499566⟩, true⟩

def words02 : List Nat := [360580202357326830, 360580203409824221, 360580205286791358, 360580207163645853, 360580207188869455, 360580207189159682, 360580205238222694, 360580204384171354, 360580203530104725, 360580202960007309]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576074120155195, 360576077072931686⟩, ⟨92542315776350641, 92587147320032293⟩, true⟩

def words03 : List Nat := [360580202907297714, 360580201850182752, 360580201718276742, 360580203638288912, 360580204187682988, 360580204737071310, 360580204737332654, 360580204265349754, 360580203243430913, 360580203059888907]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360639203126048289, 360639206081560904⟩, ⟨(-1324287028212512238), (-1324242135256468962)⟩, true⟩

def words04 : List Nat := [360580204673533250, 360580206661170237, 360580207645520129, 360580208629814219, 360580208896041363, 360580210514149539, 360580214112122509, 360580217709830789, 360580219794611666, 360580222422247000]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224A

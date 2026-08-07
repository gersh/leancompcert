import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615039564429323, 360615062167159949⟩, ⟨(-1966298594687492240), (-1965388505221005118)⟩, true⟩

def state01 : KState := ⟨⟨360582877713525956, 360582900324186957⟩, ⟨(-49372085393707028), (-48461523236611968)⟩, true⟩

def words00 : List Nat := [360582086815497615, 360582087132857981, 360582087571863385, 360582088011097331, 360582088204305852, 360582088205139474, 360582088118031496, 360582087847343902, 360582087576510123, 360582087361424437]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572813813151004, 360572836431676123⟩, ⟨550668465721383399, 551579496697827907⟩, true⟩

def words01 : List Nat := [360582087657308380, 360582087953356764, 360582088092013489, 360582088092847581, 360582088069795419, 360582087974835315, 360582088065264116, 360582088170211337, 360582088170968885, 360582088016659314]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360640323547703903, 360640346174088126⟩, ⟨(-3474614723858196367), (-3473703224282590369)⟩, true⟩

def words02 : List Nat := [360582087988482148, 360582088289721868, 360582088812537166, 360582089335495570, 360582089615394732, 360582089901382681, 360582090468620291, 360582091036083718, 360582091884707508, 360582092862483716]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611570417942551, 360611593052279977⟩, ⟨(-1759932745205424225), (-1759020771341434567)⟩, true⟩

def words03 : List Nat := [360582093605705861, 360582094348985846, 360582095081491644, 360582095958389073, 360582096762968463, 360582097567659442, 360582098213511095, 360582098579379243, 360582099074596180, 360582099570089179]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595227876946095, 360595250519134790⟩, ⟨(-785194326867625726), (-784281884714812722)⟩, true⟩

def words04 : List Nat := [360582100075883402, 360582100539410082, 360582100843843295, 360582101148354767, 360582101338360282, 360582101668047068, 360582101989006909, 360582102310104264, 360582102456497975, 360582102677778991]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360618294801278327, 360618317451340870⟩, ⟨(-2161310133100558764), (-2160397221233688288)⟩, true⟩

def words05 : List Nat := [360582103180087612, 360582103682632858, 360582104033630333, 360582104390675128, 360582104469525461, 360582104548438067, 360582104695392716, 360582105022149756, 360582105629804251, 360582106237629506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616977102760448, 360616999760790147⟩, ⟨(-2082842072467542300), (-2081928685243214304)⟩, true⟩

def words06 : List Nat := [360582106626419862, 360582106886176559, 360582107426888601, 360582107967833734, 360582108436553860, 360582108625637581, 360582108673224570, 360582108720915771, 360582109049494093, 360582109635180669]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584595796938065, 360584618462816231⟩, ⟨(-150404946813940270), (-149491091231703452)⟩, true⟩

def words07 : List Nat := [360582110501607433, 360582111368165208, 360582112093246096, 360582112538693117, 360582112728262585, 360582112918028719, 360582113322119172, 360582113541693891, 360582113584418286, 360582113627253293]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607602398072218, 360607625071841780⟩, ⟨(-1523507177514987457), (-1522592850935940969)⟩, true⟩

def words08 : List Nat := [360582113832931043, 360582114275656200, 360582114800488961, 360582115325461319, 360582115586350354, 360582115804727372, 360582116115994835, 360582116427503660, 360582116730368626, 360582117158572846]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614662549343210, 360614685231059728⟩, ⟨(-1944976971976457501), (-1944062171004219241)⟩, true⟩

def words09 : List Nat := [360582117428666795, 360582117698842981, 360582118249656152, 360582118939924054, 360582119558109928, 360582120176430359, 360582120562941803, 360582120828503549, 360582121374645761, 360582121921048100]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578835439515061, 360578863383381892⟩, ⟨268173665615986354, 269419493096494586⟩, true⟩

def state01 : KState := ⟨⟨360583043130144772, 360583071082784215⟩, ⟨(-9667457817108099), (-8421051301642033)⟩, true⟩

def words00 : List Nat := [360582945441853424, 360582945442784081, 360582945295280458, 360582944970982342, 360582944646541927, 360582944221079541, 360582943936786259, 360582943832959300, 360582943729033681, 360582943512359564]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591617325948377, 360591645287365887⟩, ⟨(-575763994616627031), (-574517008616751019)⟩, true⟩

def words01 : List Nat := [360582943513119232, 360582943438586050, 360582943472119511, 360582943515253308, 360582943516120562, 360582943358198703, 360582943200116653, 360582943036991934, 360582943120261701, 360582943253034133]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587016141770949, 360587044112055620⟩, ⟨(-272083279647398913), (-270835708194737405)⟩, true⟩

def words02 : List Nat := [360582943253863670, 360582943243983642, 360582943327897992, 360582943457836387, 360582943470860488, 360582943471791317, 360582943256064494, 360582942896090600, 360582942535946983, 360582942467249473]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567493639257419, 360567521618318359⟩, ⟨1017031191794840014, 1018279342788582746⟩, true⟩

def words03 : List Nat := [360582942524872172, 360582942582658227, 360582942583503043, 360582942431821899, 360582942108107579, 360582941695423062, 360582941282478018, 360582941098698689, 360582940980798742, 360582940748281845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603672530626964, 360603700518475290⟩, ⟨(-1372385293542662321), (-1371136562187031201)⟩, true⟩

def words04 : List Nat := [360582940515556554, 360582940624154889, 360582940923942120, 360582941223906873, 360582941272925269, 360582941273856562, 360582941142455556, 360582941191853579, 360582941447681489, 360582941762935071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660A

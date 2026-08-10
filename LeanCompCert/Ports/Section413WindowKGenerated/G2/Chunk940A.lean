import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576642725977074, 360576701003564991⟩, ⟨500223152995349140, 503922287962423732⟩, true⟩

def state01 : KState := ⟨⟨360598624290822776, 360598682581275383⟩, ⟨(-1566255708203216858), (-1562555363891367544)⟩, true⟩

def words00 : List Nat := [360582061823041007, 360582061783397794, 360582061784522592, 360582061747178062, 360582061709739995, 360582061575706941, 360582061423535570, 360582061384845403, 360582061418643048, 360582061596881096]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594336492189658, 360594394795601908⟩, ⟨(-1163138145210375082), (-1159436582498220452)⟩, true⟩

def words01 : List Nat := [360582061718157131, 360582061839582263, 360582062028091887, 360582062273491089, 360582062490036498, 360582062706806159, 360582062811186989, 360582062853845688, 360582062986108993, 360582063118822272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591646412000005, 360591704728230042⟩, ⟨(-910203828088470564), (-906501060182571990)⟩, true⟩

def words02 : List Nat := [360582063342086676, 360582063487985990, 360582063568108995, 360582063648392616, 360582063699663064, 360582063807562719, 360582063953622962, 360582064099947468, 360582064175292484, 360582064279227239]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360593921560344563, 360593979889436024⟩, ⟨(-1124193772089023461), (-1120489794758095307)⟩, true⟩

def words03 : List Nat := [360582064334634154, 360582064390431989, 360582064558823278, 360582064614758429, 360582064616014013, 360582064575851530, 360582064586106026, 360582064726242689, 360582064854054020, 360582064982164110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590983578953965, 360591041921029558⟩, ⟨(-847978717513973792), (-844273519097750110)⟩, true⟩

def words04 : List Nat := [360582065044046170, 360582065072635729, 360582065190654722, 360582065309075395, 360582065349447952, 360582065350810007, 360582065316616872, 360582065194355134, 360582065071834863, 360582065158218980]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940A

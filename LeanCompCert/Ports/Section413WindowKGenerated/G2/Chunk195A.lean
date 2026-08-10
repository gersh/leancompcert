import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360512829450657903, 360512831652818521⟩, ⟨1380047746540943732, 1380076809584522022⟩, true⟩

def state01 : KState := ⟨⟨360556470919756161, 360556473124266814⟩, ⟨528919987614796625, 528949096495999437⟩, true⟩

def words00 : List Nat := [360583601193535429, 360583600182166734, 360583599304737791, 360583596464073342, 360583593623659275, 360583589629860300, 360583586976440591, 360583586939430145, 360583586902400005, 360583584815527501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621251766044466, 360621253972911034⟩, ⟨(-735428519957862951), (-735399365100853495)⟩, true⟩

def words01 : List Nat := [360583583990926373, 360583584555901818, 360583584556105175, 360583584544173528, 360583584182385150, 360583581583260065, 360583578984348935, 360583577894521330, 360583579824850379, 360583581755037931]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559094483147156, 360559096692397091⟩, ⟨477723874930278159, 477753076322040227⟩, true⟩

def words02 : List Nat := [360583582310669838, 360583582310919667, 360583581442427794, 360583580506719410, 360583579571042780, 360583576735884942, 360583573190308010, 360583567994395191, 360583562798966906, 360583559215506259]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360423858239798527, 360423860451400161⟩, ⟨3119934409371417861, 3119963656703905547⟩, true⟩

def words03 : List Nat := [360583559320258715, 360583560677417607, 360583560677640749, 360583560179008416, 360583557069904076, 360583553294600263, 360583549519611677, 360583545679509125, 360583539229825470, 360583531058191559]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570416557495845, 360570418771456031⟩, ⟨255489117157456647, 255518410587732437⟩, true⟩

def words04 : List Nat := [360583522887337771, 360583517324139269, 360583513093518620, 360583511469863487, 360583509846350703, 360583505995264941, 360583500905629445, 360583496208429990, 360583491511635564, 360583488766882514]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195A

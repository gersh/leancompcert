import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494074586079203, 362494191012317755⟩, ⟨(-797932588645231149), (-791030567811460043)⟩, true⟩

def state01 : KState := ⟨⟨362491374318658465, 362491490772536436⟩, ⟨(-560861503905077190), (-553957056193069616)⟩, true⟩

def words00 : List Nat := [371285181729236813, 371285181732330199, 371285181851375219, 371285181978332458, 371285182115164882, 371285182118224017, 371285182104061977, 371285182091057745, 371285182181686347, 371285182257017959]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488077615358358, 362488194096704779⟩, ⟨(-271319414914376214), (-264412555053581292)⟩, true⟩

def words01 : List Nat := [371285182460529454, 371285182665256987, 371285182844035067, 371285182894188078, 371285182947895436, 371285183003094220, 371285183173209018, 371285183210050863, 371285183246621584, 371285183284313056]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494585635225845, 362494702144000655⟩, ⟨(-842827743898472480), (-835918475139923614)⟩, true⟩

def words02 : List Nat := [371285183432614406, 371285183542919040, 371285183761637808, 371285183981658566, 371285184180738928, 371285184207746998, 371285184347119732, 371285184488060072, 371285184681251441, 371285184792779106]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492986992239275, 362493103528935749⟩, ⟨(-702382753597669933), (-695471032341514199)⟩, true⟩

def words03 : List Nat := [371285184902051191, 371285185012358065, 371285185250911903, 371285185426008659, 371285185605344634, 371285185785864037, 371285185946374226, 371285185957523759, 371285186049739874, 371285186143747267]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485163916588396, 362485280480550341⟩, ⟨(-15182813462780298), (-8268697066029086)⟩, true⟩

def words04 : List Nat := [371285186291961363, 371285186295020656, 371285186284164083, 371285186244979725, 371285186204651507, 371285186205254797, 371285186225809798, 371285186296271730, 371285186354420575, 371285186358718307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598949863675666, 360598951704886473⟩, ⟨(-270410528014988792), (-270388219182930308)⟩, true⟩

def state01 : KState := ⟨⟨360613295648735949, 360613297492112488⟩, ⟨(-527880324833362411), (-527857977224052841)⟩, true⟩

def words00 : List Nat := [360583847061822029, 360583845580536115, 360583841004880361, 360583839534353027, 360583838063930086, 360583835798006450, 360583833656997473, 360583829631591169, 360583825606589379, 360583826330411631]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547792412512811, 360547794258034539⟩, ⟨645943082696346822, 645965468736957116⟩, true⟩

def words01 : List Nat := [360583831078364486, 360583835825830687, 360583838135131244, 360583840160072593, 360583841390689504, 360583842621229002, 360583843130548130, 360583843449438061, 360583843449643888, 360583841438209593]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360662875607627393, 360662877455295716⟩, ⟨(-1416794966129957444), (-1416772541611612844)⟩, true⟩

def words02 : List Nat := [360583840515291640, 360583843650290124, 360583849884099708, 360583856117257231, 360583859656501710, 360583860108571368, 360583860108759532, 360583859233779716, 360583860581572232, 360583864988528017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360648536822788335, 360648538672623736⟩, ⟨(-1159643219825059303), (-1159620756440494005)⟩, true⟩

def words03 : List Nat := [360583867515676174, 360583870042567391, 360583874633769109, 360583881751078744, 360583886940377451, 360583892129134734, 360583895722085159, 360583896230769318, 360583899834211264, 360583903437328018]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554215903231762, 360554217755214228⟩, ⟨532540164271144324, 532562666185002930⟩, true⟩

def words04 : List Nat := [360583905314604149, 360583905314832034, 360583904108706704, 360583901348032272, 360583898587628526, 360583894051845595, 360583891113000417, 360583890325145684, 360583889537350144, 360583886984528156]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179A

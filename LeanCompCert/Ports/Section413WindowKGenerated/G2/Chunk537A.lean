import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk537A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586346117273837, 360586364313320708⟩, ⟨(-237208382672418382), (-236548173424375848)⟩, true⟩

def state01 : KState := ⟨⟨360595800444833759, 360595818647897478⟩, ⟨(-744976418146786893), (-744315832059266625)⟩, true⟩

def words00 : List Nat := [360581959750729723, 360581960047607626, 360581960086028705, 360581960124531153, 360581960125155662, 360581960014775042, 360581960267024540, 360581960519407870, 360581960597748295, 360581960856531478]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612395148445308, 360612413358555206⟩, ⟨(-1636541681742495196), (-1635880717169611528)⟩, true⟩

def words01 : List Nat := [360581961106506755, 360581961356688494, 360581961513625870, 360581961514371359, 360581961416160900, 360581961023066586, 360581960629840599, 360581960803758721, 360581961371236946, 360581961938865148]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573619663281230, 360573637880493820⟩, ⟨446531148550864776, 447192494714481766⟩, true⟩

def words02 : List Nat := [360581962296954103, 360581962309251517, 360581962531353268, 360581962753670948, 360581962754306354, 360581962731324636, 360581962362434665, 360581961819830967, 360581961277106355, 360581960837774939]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360529034826409641, 360529053050649454⟩, ⟨2842439862517233617, 2843101586289070079⟩, true⟩

def words03 : List Nat := [360581960874392773, 360581961066061383, 360581961083893459, 360581961084639216, 360581960866442568, 360581960422069614, 360581959977496747, 360581959503296628, 360581958790332178, 360581957806628038]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596316464224489, 360596334695501889⟩, ⟨(-773617474148033459), (-772955372142061941)⟩, true⟩

def words04 : List Nat := [360581956822791666, 360581956079917279, 360581955570820354, 360581955328296842, 360581955085724141, 360581954548710182, 360581954202525039, 360581954101961386, 360581954129665555, 360581954397979200]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk537A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580831550662700, 360580866011362335⟩, ⟨111027766054082716, 112726926334265734⟩, true⟩

def state01 : KState := ⟨⟨360600666854000957, 360600701324506564⟩, ⟨(-1337091472543407036), (-1335391596379461768)⟩, true⟩

def words00 : List Nat := [360582410281843058, 360582410487645464, 360582410689034844, 360582410890602643, 360582410932901688, 360582410933939092, 360582410830514785, 360582410756190863, 360582410793398921, 360582411045009236]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607510610857731, 360607545091234535⟩, ⟨(-1836806912405948479), (-1835106315496442843)⟩, true⟩

def words01 : List Nat := [360582411202939965, 360582411360979357, 360582411706128231, 360582412160520846, 360582412502716737, 360582412845070004, 360582413029777575, 360582413187713995, 360582413532731263, 360582413878083573]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595230308708119, 360595264798854222⟩, ⟨(-940094846016939666), (-938393535704332852)⟩, true⟩

def words02 : List Nat := [360582414206157516, 360582414435009640, 360582414552657097, 360582414670432370, 360582414678271001, 360582414779944845, 360582415024986043, 360582415270219104, 360582415372397068, 360582415549416253]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360632638994424235, 360632673494385156⟩, ⟨(-3672336344533443824), (-3670634317398595712)⟩, true⟩

def words03 : List Nat := [360582415722120104, 360582415895112150, 360582416225659482, 360582416539306891, 360582416689672132, 360582416840106952, 360582417177536884, 360582417679578120, 360582418368476060, 360582419057597618]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613289417227966, 360613323927063127⟩, ⟨(-2259027115242916728), (-2257324366843576354)⟩, true⟩

def words04 : List Nat := [360582419628951327, 360582420077151663, 360582420712325022, 360582421347796182, 360582421853984729, 360582422173283159, 360582422373870989, 360582422574563503, 360582422839404923, 360582423263597281]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk730A

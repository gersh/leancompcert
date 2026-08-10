import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360528033626500372, 360528039981660209⟩, ⟨1730819359016709021, 1730958590995177865⟩, true⟩

def state01 : KState := ⟨⟨360555762028274889, 360555768387507993⟩, ⟨832249065500218399, 832388429473451497⟩, true⟩

def words00 : List Nat := [360581462981021818, 360581462281777118, 360581461284030016, 360581459547752261, 360581457811511311, 360581455836562083, 360581454575069806, 360581453739013645, 360581452902967342, 360581451461542966]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587258976310556, 360587265339618160⟩, ⟨(-188606697032763609), (-188467200984099547)⟩, true⟩

def words01 : List Nat := [360581450825589458, 360581450982171403, 360581452087043754, 360581452802905959, 360581452803304283, 360581452706392039, 360581452609411588, 360581451996757144, 360581452038708792, 360581452218462610]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624927902830993, 360624934270254562⟩, ⟨(-1410234560002112337), (-1410094930493978495)⟩, true⟩

def words02 : List Nat := [360581452218847735, 360581451829587799, 360581452410881510, 360581453175782173, 360581453690290916, 360581453690723511, 360581453664081949, 360581453154186329, 360581453081648460, 360581454422871072]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549867798129966, 360549874169631228⟩, ⟨1024269196547188612, 1024408958315201750⟩, true⟩

def words03 : List Nat := [360581455447608809, 360581456472359889, 360581456900430467, 360581456900862902, 360581456379730830, 360581455329993423, 360581454280188560, 360581453960918263, 360581453717206583, 360581452744178553]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360629127839301861, 360629134214883655⟩, ⟨(-1547292280554045629), (-1547152386393288263)⟩, true⟩

def words04 : List Nat := [360581451771112854, 360581452200964988, 360581453603959904, 360581455006951044, 360581455496609899, 360581455497042477, 360581455238895539, 360581455440126870, 360581456174790160, 360581457644473089]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324A

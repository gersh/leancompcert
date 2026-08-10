import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576509523175859, 360576550669579931⟩, ⟨448543507501604608, 450752783537838666⟩, true⟩

def state01 : KState := ⟨⟨360580016488187371, 360580057645294559⟩, ⟨169713161096316746, 171923288083789510⟩, true⟩

def words00 : List Nat := [360582220500636495, 360582220501773003, 360582220437517836, 360582220294287650, 360582220150875895, 360582219968403386, 360582219951060157, 360582219995261799, 360582219996277328, 360582219930391828]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582209367143253, 360582250534990149⟩, ⟨(-4699386398681047), (-2488405445035655)⟩, true⟩

def words01 : List Nat := [360582219950361991, 360582219997857974, 360582219998793522, 360582219997360428, 360582219875546542, 360582219630166547, 360582219384575109, 360582219263816456, 360582219240967829, 360582219242558653]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576392668749858, 360576433847420394⟩, ⟨457751218359204140, 459963060061209454⟩, true⟩

def words02 : List Nat := [360582219243576415, 360582219144764614, 360582218887959794, 360582218767406529, 360582218646544091, 360582218484418770, 360582218269972987, 360582217930309649, 360582217590437392, 360582217363830066]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582899037978915, 360582940227345859⟩, ⟨(-59648784833552359), (-57436092392294645)⟩, true⟩

def words03 : List Nat := [360582217377132912, 360582217463371800, 360582217469990410, 360582217598554852, 360582217687540388, 360582217776825030, 360582218023573019, 360582218112828061, 360582218122919737, 360582218133175654]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587561759028295, 360587602959147224⟩, ⟨(-430621370243875043), (-428407822538060397)⟩, true⟩

def words04 : List Nat := [360582218134117271, 360582218070007695, 360582218131608840, 360582218193423927, 360582218194472733, 360582218121221628, 360582217953919670, 360582217773020549, 360582217591770514, 360582217636240686]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573664826010555, 360573702604512461⟩, ⟨645046768927848147, 646993646207951715⟩, true⟩

def state01 : KState := ⟨⟨360588329663182280, 360588367451945722⟩, ⟨(-473927090190407725), (-471979429903969925)⟩, true⟩

def words00 : List Nat := [360582182096437032, 360582182172955337, 360582182430327948, 360582182687904386, 360582182799403339, 360582182800491031, 360582182740538286, 360582182590774011, 360582182440694661, 360582182505740012]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591882187215103, 360591919986343722⟩, ⟨(-745079324846679099), (-743130873542504665)⟩, true⟩

def words01 : List Nat := [360582182506718595, 360582182486185713, 360582182467489838, 360582182611642783, 360582182712136054, 360582182812804039, 360582182827379113, 360582182828474333, 360582182945343303, 360582183074176134]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582064247623798, 360582102057015237⟩, ⟨4205516015837413, 6154750628295987⟩, true⟩

def words02 : List Nat := [360582183198629475, 360582183221253498, 360582183222229716, 360582183121129123, 360582183019855402, 360582182831895360, 360582182760103988, 360582182791763010, 360582182792749120, 360582182690457243]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599319713300298, 360599357532959086⟩, ⟨(-1313017828149851332), (-1311067809778683596)⟩, true⟩

def words03 : List Nat := [360582182788026245, 360582182886967821, 360582183156981208, 360582183255981411, 360582183257002571, 360582183193214710, 360582183143679135, 360582183245065183, 360582183470916160, 360582183697015378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597302553941392, 360597340383971263⟩, ⟨(-1159004266086969954), (-1157053455935716142)⟩, true⟩

def words04 : List Nat := [360582183837077767, 360582184068699169, 360582184471422695, 360582184874454948, 360582185233954879, 360582185479764868, 360582185605946082, 360582185732230828, 360582185786056054, 360582185985784786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584826631071239, 360584840357856568⟩, ⟨(-91079163209018118), (-90644126541867706)⟩, true⟩

def state01 : KState := ⟨⟨360601178324576721, 360601192057439806⟩, ⟨(-858013611388275333), (-857578289643802535)⟩, true⟩

def words00 : List Nat := [360582908183601260, 360582908907070210, 360582909592384280, 360582910277798373, 360582910544611454, 360582910545255981, 360582910514006131, 360582910471971528, 360582910703337731, 360582911093707552]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590030817416997, 360590044556416237⟩, ⟨(-335032539295641162), (-334596929674149992)⟩, true⟩

def words01 : List Nat := [360582911201850583, 360582911310058288, 360582911706504731, 360582912449316826, 360582912889133296, 360582913329032988, 360582913481732931, 360582913482377449, 360582913333818413, 360582913486539761]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599932344857283, 360599946089935338⟩, ⟨(-799798430144381128), (-799362535275242920)⟩, true⟩

def words02 : List Nat := [360582913628207735, 360582913628852856, 360582913536951238, 360582913218644459, 360582912900246670, 360582912464314552, 360582912667816887, 360582912950793503, 360582913007327212, 360582913370937762]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360621988729066747, 360622002480222340⟩, ⟨(-1835003215005586630), (-1834567034886770422)⟩, true⟩

def words03 : List Nat := [360582914060543779, 360582914750309324, 360582915892568905, 360582916770796609, 360582917205405053, 360582917640029521, 360582917911929726, 360582918411736031, 360582919244896190, 360582920078166850]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576310719564368, 360576324476867835⟩, ⟨309285715327289499, 309722184057508237⟩, true⟩

def words04 : List Nat := [360582920685103521, 360582921310958230, 360582921857015746, 360582922403242436, 360582922718747570, 360582922719392437, 360582922582342672, 360582922219259350, 360582921856073805, 360582921328498453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360551358875773632, 360551372639150300⟩, ⟨1480975269037196314, 1481412022934207368⟩, true⟩

def words05 : List Nat := [360582921295233787, 360582921402592663, 360582921403173504, 360582921193704112, 360582920838293255, 360582920368714915, 360582919898951679, 360582919881583833, 360582919562883419, 360582918891768150]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591664549315603, 360591678318790491⟩, ⟨(-412031257438609715), (-411594217139715895)⟩, true⟩

def words06 : List Nat := [360582918220535433, 360582917898794041, 360582917807085351, 360582917704741778, 360582917602352606, 360582917108991044, 360582916409873045, 360582916029368476, 360582915648691975, 360582915588230365]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582828866929413, 360582842642545926⟩, ⟨3021701777618867, 3459030579108053⟩, true⟩

def words07 : List Nat := [360582915588812040, 360582915455935736, 360582915542654203, 360582915990350561, 360582916320800038, 360582916651340160, 360582916651924911, 360582916630059339, 360582916271095444, 360582916270272174]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585718156485175, 360585731938178360⟩, ⟨(-132782541192781229), (-132344926878834137)⟩, true⟩

def words08 : List Nat := [360582916338950969, 360582916339599466, 360582916320090899, 360582916075034379, 360582915829871871, 360582915470834820, 360582915532184906, 360582915663108305, 360582915663689453, 360582915549361803]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360616604698858572, 360616618486653953⟩, ⟨(-1584430584117501591), (-1583992683031650287)⟩, true⟩

def words09 : List Nat := [360582915560410732, 360582915571644045, 360582916034098096, 360582916045109789, 360582916045707755, 360582915669223191, 360582915366878430, 360582915796404621, 360582916514005318, 360582917231722534]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk702A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552462394242466, 360552494163228577⟩, ⟨2106392902679386348, 2107899309857089588⟩, true⟩

def state01 : KState := ⟨⟨360573010959585214, 360573042737946825⟩, ⟨663739617450878615, 665246682835862647⟩, true⟩

def words00 : List Nat := [360582520791998856, 360582520567703563, 360582520313809749, 360582519902170824, 360582519490383403, 360582518982177393, 360582518575903876, 360582518372233031, 360582518168468828, 360582517836691105]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560050768040155, 360560082555784217⟩, ⟨1573731489988741553, 1575239214162001797⟩, true⟩

def words01 : List Nat := [360582517710744748, 360582517720041557, 360582517720855055, 360582517664714752, 360582517405999804, 360582516976439630, 360582516546715408, 360582516107570479, 360582515788126747, 360582515469685699]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565242887896492, 360565274685117725⟩, ⟨1208967562954097596, 1210475952660019038⟩, true⟩

def words02 : List Nat := [360582515151110640, 360582514717308999, 360582514080864082, 360582513647077704, 360582513213012416, 360582512704207110, 360582512224437540, 360582511604375745, 360582510984141132, 360582510566545321]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539477853170355, 360539509659770884⟩, ⟨3018521435927011849, 3020030484388667871⟩, true⟩

def words03 : List Nat := [360582510321946919, 360582510031864311, 360582509741682045, 360582509321765566, 360582508699279403, 360582507943198270, 360582507186836581, 360582506632969268, 360582506149072302, 360582505537965484]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587647826662396, 360587679642652455⟩, ⟨(-365185023230265303), (-363675315201960905)⟩, true⟩

def words04 : List Nat := [360582504926650705, 360582504517897716, 360582504237325096, 360582504046224758, 360582503855074652, 360582503463641510, 360582503112239422, 360582502930819797, 360582502768806854, 360582502843529283]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk702A

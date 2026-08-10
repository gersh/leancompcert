import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360520562797061772, 360520572499295375⟩, ⟨2458114917119060140, 2458375254966930576⟩, true⟩

def state01 : KState := ⟨⟨360581565915579623, 360581575622885589⟩, ⟨35898708889994485, 36159248135979799⟩, true⟩

def words00 : List Nat := [360582494749924929, 360582493321061851, 360582492294446630, 360582491901019710, 360582491507561398, 360582490571018487, 360582489003352342, 360582487859897533, 360582486716337450, 360582486205815229]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590288306354847, 360590298018782834⟩, ⟨(-310617699032977723), (-310356956365996939)⟩, true⟩

def words01 : List Nat := [360582486183372549, 360582485652261998, 360582485121073855, 360582485338665430, 360582485339117678, 360582485213456730, 360582485087748275, 360582484637583767, 360582484398926093, 360582484596251529]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360556582968826936, 360556592686317804⟩, ⟨1028155942823557461, 1028416886613601233⟩, true⟩

def words02 : List Nat := [360582484615132970, 360582484615670708, 360582484004072384, 360582483075732273, 360582482147359527, 360582480755013437, 360582479684586961, 360582479246616382, 360582478808609138, 360582477833224767]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586038005009226, 360586047727580626⟩, ⟨(-142228231603968791), (-141967085939491327)⟩, true⟩

def words03 : List Nat := [360582477182149707, 360582476960542799, 360582477148668926, 360582477149206846, 360582476929326973, 360582476170924937, 360582475412458202, 360582475238950945, 360582475329290107, 360582475419738864]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599066812682937, 360599076540378751⟩, ⟨(-660354375864347692), (-660093026530421594)⟩, true⟩

def words04 : List Nat := [360582475420220336, 360582475107981437, 360582474429131044, 360582473845631358, 360582473262011880, 360582472518800929, 360582472074956783, 360582471314937412, 360582470554852171, 360582470844257134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397A

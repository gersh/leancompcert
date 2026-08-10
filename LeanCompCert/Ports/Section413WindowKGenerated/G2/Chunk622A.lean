import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576343702703322, 360576368404023957⟩, ⟨390437909523402232, 391475823914884678⟩, true⟩

def state01 : KState := ⟨⟨360607637423391019, 360607662132963536⟩, ⟨(-1556119317065807987), (-1555080889366180025)⟩, true⟩

def words00 : List Nat := [360582662284256746, 360582662644194145, 360582663091169235, 360582663538295270, 360582663738253676, 360582663824349852, 360582664168588091, 360582664513081228, 360582664850443445, 360582665253161473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615352911018778, 360615377628902461⟩, ⟨(-2036165601769219552), (-2035126656991528142)⟩, true⟩

def words01 : List Nat := [360582665509243512, 360582665765412732, 360582666279677669, 360582666922515037, 360582667424975505, 360582667927582462, 360582668272283140, 360582668540633127, 360582669067039473, 360582669593721549]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608273552387744, 360608298278501114⟩, ⟨(-1595708134592333026), (-1594668677722061414)⟩, true⟩

def words02 : List Nat := [360582670281895695, 360582670800323183, 360582671121332486, 360582671442413367, 360582671626400642, 360582671942541285, 360582672297272279, 360582672652154676, 360582672877007263, 360582673289705786]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360632425946716831, 360632450681069283⟩, ⟨(-3098865899355530410), (-3097825929726501636)⟩, true⟩

def words03 : List Nat := [360582673777721746, 360582674265974808, 360582675012060359, 360582675705296945, 360582676179791642, 360582676654330956, 360582677016960753, 360582677612254971, 360582678412656852, 360582679213230937]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604135761514299, 360604160504184088⟩, ⟨(-1338046759936051006), (-1337006272596772246)⟩, true⟩

def words04 : List Nat := [360582679883806057, 360582680297450306, 360582680891980450, 360582681486780153, 360582681963214666, 360582682182787928, 360582682272462474, 360582682362230260, 360582682490775549, 360582682836795665]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622A

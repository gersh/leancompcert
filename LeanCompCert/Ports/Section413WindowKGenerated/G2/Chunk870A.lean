import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571399746986856, 360571449368952704⟩, ⟨930247570243377800, 933162948801425212⟩, true⟩

def state01 : KState := ⟨⟨360575742643205249, 360575792276981432⟩, ⟨552329547277357212, 555245953392805016⟩, true⟩

def words00 : List Nat := [360582175257586619, 360582175184423462, 360582175033847695, 360582174780385303, 360582174526724476, 360582174240175728, 360582174046260111, 360582173959604228, 360582173872820745, 360582173680882051]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592447470450932, 360592497116026696⟩, ⟨(-901231975827707140), (-898314542970565410)⟩, true⟩

def words01 : List Nat := [360582173667131309, 360582173727100218, 360582173918599764, 360582174007241646, 360582174008396557, 360582173984715215, 360582173960812642, 360582173913690102, 360582174033332602, 360582174153259427]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582433768834042, 360582483426349405⟩, ⟨(-29882581049256343), (-26964109150287005)⟩, true⟩

def words02 : List Nat := [360582174174179302, 360582174175437680, 360582174184865733, 360582174212946731, 360582174213996215, 360582174187438057, 360582174072220350, 360582173891058789, 360582173709662181, 360582173604456628]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561397112905953, 360561446782232650⟩, ⟨1801019272556158547, 1803938772455689305⟩, true⟩

def words03 : List Nat := [360582173605678030, 360582173607132684, 360582173608248648, 360582173529544864, 360582173318752715, 360582173027074679, 360582172735035412, 360582172575100915, 360582172418548358, 360582172181732371]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580977810092478, 360581027491239840⟩, ⟨96610149343244313, 99530678171158055⟩, true⟩

def words04 : List Nat := [360582171944634028, 360582171839736268, 360582171813056045, 360582171761940312, 360582171710748144, 360582171533768105, 360582171264606611, 360582171087601091, 360582170910209705, 360582170864912111]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk870A

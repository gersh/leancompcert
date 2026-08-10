import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492592953051464, 362492696029686876⟩, ⟨(-619013674806390369), (-613250727849636709)⟩, true⟩

def state01 : KState := ⟨⟨362489761551275484, 362489864653510165⟩, ⟨(-384554815767435012), (-378789749058997524)⟩, true⟩

def words00 : List Nat := [371285289921778496, 371285289983947283, 371285290017863632, 371285290052685045, 371285290131038910, 371285290142227971, 371285290243512204, 371285290346003796, 371285290447487771, 371285290505763381]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503936458159271, 362504039586279467⟩, ⟨(-1558412130726802371), (-1552644920307563693)⟩, true⟩

def words01 : List Nat := [371285290708833938, 371285290913357668, 371285291262303249, 371285291444094429, 371285291601775781, 371285291760388477, 371285291977704482, 371285292132824617, 371285292361148793, 371285292590706997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489468681970067, 362489571835997438⟩, ⟨(-360181081958145460), (-354411725778239470)⟩, true⟩

def words02 : List Nat := [371285292813972720, 371285292843609197, 371285292933385287, 371285293024734500, 371285293157325992, 371285293160197072, 371285293098606214, 371285293037877581, 371285293048131401, 371285293103086110]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486613206940919, 362486716386876359⟩, ⟨(-123641476295880619), (-117869974022052095)⟩, true⟩

def words03 : List Nat := [371285293216614241, 371285293331314633, 371285293444719774, 371285293447591575, 371285293385448825, 371285293369311876, 371285293477865801, 371285293501255286, 371285293520578910, 371285293541014744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489535383462787, 362489638589089692⟩, ⟨(-365723468784185151), (-359949838097050965)⟩, true⟩

def words04 : List Nat := [371285293598123483, 371285293601288366, 371285293680589722, 371285293778546005, 371285293839265364, 371285293842141515, 371285293792633510, 371285293843268474, 371285293989394784, 371285294044810238]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828A

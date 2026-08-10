import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274A

def state06 : KState := ⟨⟨360534205283901748, 360534209784768509⟩, ⟨1336672652770475174, 1336756250112158896⟩, true⟩

def words05 : List Nat := [360582895603816170, 360582895599254859, 360582895594654525, 360582894923674482, 360582894773883064, 360582893670167957, 360582892784864049, 360582892785225546, 360582891682865403, 360582889910409885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556271316856678, 360556275821140613⟩, ⟨730604040613081232, 730687731807230326⟩, true⟩

def words06 : List Nat := [360582888138006988, 360582886331863992, 360582885346672698, 360582885055842907, 360582884765006054, 360582883347544828, 360582881174011134, 360582879088329628, 360582877002685293, 360582875301730611]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567659643486687, 360567664151211615⟩, ⟨417629060590070910, 417712846325512598⟩, true⟩

def words07 : List Nat := [360582874333777905, 360582872700559538, 360582871067390077, 360582870528344951, 360582870528653280, 360582869703747100, 360582868878864616, 360582867190030111, 360582865317011030, 360582864764251117]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608788063579136, 360608792574716299⟩, ⟨(-712614568803186707), (-712530689282422557)⟩, true⟩

def words08 : List Nat := [360582864978228228, 360582866356332295, 360582867069917689, 360582867783490682, 360582867783793980, 360582868404142553, 360582870369866411, 360582872335516399, 360582872942138107, 360582873885353147]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360658236600488336, 360658241115040958⟩, ⟨(-2072317687751940495), (-2072233714323550503)⟩, true⟩

def words09 : List Nat := [360582875573598385, 360582877261826763, 360582879506024690, 360582880949974219, 360582881260621273, 360582881571275566, 360582882663021587, 360582884420879164, 360582887161415413, 360582889901836946]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274B

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517485155868120, 360517489636233638⟩, ⟨1794006670913186007, 1794089705906676681⟩, true⟩

def state01 : KState := ⟨⟨360576326799282399, 360576331283051417⟩, ⟨181285155437884443, 181368283703759271⟩, true⟩

def words00 : List Nat := [360582964973409668, 360582962312081780, 360582960319066016, 360582959230036225, 360582958141064194, 360582955768642725, 360582952535900649, 360582950630918513, 360582948725970088, 360582948148564141]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360526119651362274, 360526124138571434⟩, ⟨1557880992950149722, 1557964215527338810⟩, true⟩

def words01 : List Nat := [360582947907491049, 360582946997606878, 360582946102545317, 360582946793132680, 360582947144368774, 360582947495638539, 360582947495962411, 360582946782149300, 360582944744875616, 360582942673054561]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360525671288370352, 360525675778978142⟩, ⟨1569953391148450190, 1570036706933446016⟩, true⟩

def words02 : List Nat := [360582940601266367, 360582938975484303, 360582936026529887, 360582932061397603, 360582928096496073, 360582923791169730, 360582920502956777, 360582918540242213, 360582916577631599, 360582913719442359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620817732159081, 360620822226181063⟩, ⟨(-1040449640557911500), (-1040366231105209274)⟩, true⟩

def words03 : List Nat := [360582911633119351, 360582910872028667, 360582910110889076, 360582909315623903, 360582908999909321, 360582907506724054, 360582906013577942, 360582906622493956, 360582908004550624, 360582909386594124]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557089344770444, 360557093842233417⟩, ⟨708200645289223214, 708284149179742686⟩, true⟩

def words04 : List Nat := [360582910101868739, 360582910102230033, 360582909495318810, 360582909272527739, 360582909049659587, 360582907954143628, 360582905536762964, 360582902097675947, 360582898658770391, 360582896543478581]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274

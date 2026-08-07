import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk115

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362427625800026175, 362427627486114565⟩, ⟨671495287672591912, 671508411567547680⟩, true⟩

def state01 : KState := ⟨⟨362473942466412948, 362473944155549873⟩, ⟨138772684907437585, 138785843876068545⟩, true⟩

def words00 : List Nat := [371286014445011629, 371286011548343683, 371286006188148673, 371286007273021126, 371286007273285744, 371286007198652061, 371286000429276653, 371285999348893659, 371286002004361888, 371286002004713737]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491526445066691, 362491528137308810⟩, ⟨(-63681660680844208), (-63668465955931166)⟩, true⟩

def words01 : List Nat := [371286000957464198, 371285999854845893, 371286003045818608, 371286004457998606, 371286006146007311, 371286007833844977, 371286007908566769, 371286007908908777, 371286001360320870, 371286001840463404]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480302414902784, 362480304110182586⟩, ⟨65912372470870506, 65925602205787246⟩, true⟩

def words02 : List Nat := [371286007914622661, 371286007914969022, 371286007746847852, 371286006772899421, 371286007094367746, 371286007094743695, 371286011591675002, 371286017588436778, 371286021855034344, 371286021855386905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362565439986961148, 362565441685319595⟩, ⟨(-916094807605145111), (-916081542357586769)⟩, true⟩

def words03 : List Nat := [371286025772908969, 371286030185694785, 371286039980089448, 371286041404949441, 371286041626482638, 371286041848093674, 371286048603628534, 371286051655903653, 371286058535689220, 371286065414428201]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489548592237766, 362489550293680390⟩, ⟨(-40386039734195182), (-40372738879728296)⟩, true⟩

def words04 : List Nat := [371286072302074311, 371286072302415811, 371286071300772083, 371286070801706455, 371286072065027599, 371286072065369429, 371286065916689419, 371286059726640609, 371286054818054493, 371286055121065056]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362408119915847977, 362408121620366748⟩, ⟨901079986756263832, 901093323156061068⟩, true⟩

def words05 : List Nat := [371286062891366369, 371286070660465796, 371286078436102315, 371286078436443900, 371286079511102786, 371286081180368358, 371286084369075617, 371286084369417229, 371286077612985528, 371286070869774712]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362453693031595191, 362453694739174105⟩, ⟨374158638259210065, 374172010049895547⟩, true⟩

def words06 : List Nat := [371286064127577387, 371286061213397901, 371286055687292068, 371286055961369749, 371286055961637100, 371286055014547745, 371286044138926298, 371286039192758749, 371286034584112555, 371286034584467960]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485263760649513, 362485265471345458⟩, ⟨8642153225169248, 8655561096043710⟩, true⟩

def words07 : List Nat := [371286031789824458, 371286027197182874, 371286024025069173, 371286024025449144, 371286021781529261, 371286021791335173, 371286021791592289, 371286020482178890, 371286012993259759, 371286012929125773]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362427938754484674, 362427940468230124⟩, ⟨672704986300573836, 672718429500653334⟩, true⟩

def words08 : List Nat := [371286018468583514, 371286018468925976, 371286014173195596, 371286008604576656, 371286003036788403, 371285997649494056, 371285988537738536, 371285986841507911, 371285985145458453, 371285983473363917]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362599674731549986, 362599676448406729⟩, ⟨(-1318357302563930041), (-1318343823289017373)⟩, true⟩

def words09 : List Nat := [371285979501749471, 371285980537738962, 371285988977902265, 371285993204009529, 371285996212802369, 371285999221180943, 371286009629705448, 371286016319898378, 371286026118422830, 371286035915410521]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk115

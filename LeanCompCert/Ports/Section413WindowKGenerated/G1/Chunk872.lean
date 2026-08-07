import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489432509629720, 362489547289434898⟩, ⟨(-386126704523099549), (-379368747306219983)⟩, true⟩

def state01 : KState := ⟨⟨362480675475705027, 362480790282926073⟩, ⟨377482491515381574, 384242839530295558⟩, true⟩

def words00 : List Nat := [371285196832618427, 371285196835654424, 371285196730079991, 371285196691118280, 371285196650670304, 371285196640876143, 371285196521078158, 371285196390935076, 371285196259510606, 371285196232238426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468266581043377, 362468381415598653⟩, ⟨1459787495309016570, 1466550227280826778⟩, true⟩

def words01 : List Nat := [371285196264596374, 371285196348681473, 371285196406453959, 371285196409489694, 371285196291904753, 371285196216145468, 371285196146787934, 371285196149823746, 371285195984981796, 371285195795640855]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476398746709751, 362476513608416330⟩, ⟨750498318942088541, 757263419192131403⟩, true⟩

def words02 : List Nat := [371285195604920493, 371285195546796399, 371285195425869604, 371285195433351740, 371285195435703738, 371285195422969451, 371285195234168985, 371285195069604813, 371285194903473543, 371285194835278558]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480663873120047, 362480778762490323⟩, ⟨378453622790593470, 385221136282611310⟩, true⟩

def words03 : List Nat := [371285194738028030, 371285194641960606, 371285194565132440, 371285194568540191, 371285194566041836, 371285194583338116, 371285194597174170, 371285194600211711, 371285194457370172, 371285194410544916]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466734410381259, 362466849326850300⟩, ⟨1593712325575327311, 1600482203300056195⟩, true⟩

def words04 : List Nat := [371285194362040526, 371285194322555148, 371285194119135891, 371285193914198978, 371285193708121790, 371285193543545487, 371285193318498714, 371285193203385240, 371285193087141781, 371285192962418209]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487383653203497, 362487498597058751⟩, ⟨(-208032013309258912), (-201259745995472976)⟩, true⟩

def words05 : List Nat := [371285192754237933, 371285192678848827, 371285192654099736, 371285192657136933, 371285192536736386, 371285192386393780, 371285192234775064, 371285192215653041, 371285192156063135, 371285192185878551]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469402908856809, 362469517880167455⟩, ⟨1361053885537723426, 1367828548745803336⟩, true⟩

def words06 : List Nat := [371285192188157517, 371285192184953951, 371285192094536104, 371285192073366521, 371285192055824699, 371285192058862382, 371285191891380384, 371285191720323326, 371285191548107860, 371285191405419499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473360508456527, 362473475507135984⟩, ⟨1015698632082384872, 1022475683909388994⟩, true⟩

def words07 : List Nat := [371285191227883601, 371285191178391131, 371285191127867901, 371285191078330988, 371285190910052102, 371285190782307285, 371285190652959967, 371285190655742771, 371285190528875402, 371285190398106532]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483342090827324, 362483457116734996⟩, ⟨144465001773851108, 151244430218091034⟩, true⟩

def words08 : List Nat := [371285190265946340, 371285190266258756, 371285190216052758, 371285190199482531, 371285190182013523, 371285190117401688, 371285189915882696, 371285189839022773, 371285189779703107, 371285189782907732]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483001848725244, 362483116902306529⟩, ⟨174182766422533366, 180964610631518400⟩, true⟩

def words09 : List Nat := [371285189765354160, 371285189740693752, 371285189817995455, 371285189858964317, 371285189906243801, 371285189954739481, 371285189977062164, 371285189980101076, 371285189827328326, 371285189807353855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872

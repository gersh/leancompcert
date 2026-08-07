import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482022847264358, 362482104010507579⟩, ⟨231483266234412524, 235528363779020012⟩, true⟩

def state01 : KState := ⟨⟨362467002855370720, 362467084041230417⟩, ⟨1340005222658328111, 1344051989416617505⟩, true⟩

def words00 : List Nat := [371285295410510118, 371285295413046772, 371285295170596996, 371285294928380796, 371285294685223679, 371285294478203217, 371285294178199274, 371285294009650971, 371285293840186569, 371285293660379809]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495400303258732, 362495481511997502⟩, ⟨(-756151077132129741), (-752102621551240315)⟩, true⟩

def words01 : List Nat := [371285293415395559, 371285293325654865, 371285293300777269, 371285293303333437, 371285293244364265, 371285293139640899, 371285293080488640, 371285293083313431, 371285293177803320, 371285293318643968]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482934921545918, 362483016153196831⟩, ⟨164099269122636959, 168149416196044665⟩, true⟩

def words02 : List Nat := [371285293421274594, 371285293423856297, 371285293504839055, 371285293639169225, 371285293828739290, 371285293831276823, 371285293776547982, 371285293720882454, 371285293671849979, 371285293674748992]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474710972294908, 362474792226841727⟩, ⟨771360056462156356, 775411894054005358⟩, true⟩

def words03 : List Nat := [371285293688747153, 371285293734661041, 371285293780133320, 371285293782679487, 371285293689971518, 371285293654532164, 371285293734153293, 371285293736691464, 371285293610662145, 371285293471344084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481445175541357, 362481526452817128⟩, ⟨274062432683564312, 278115948697101172⟩, true⟩

def words04 : List Nat := [371285293330851994, 371285293331816252, 371285293253253884, 371285293192615582, 371285293131231588, 371285293036137328, 371285292695930840, 371285292540204868, 371285292407468807, 371285292410145458]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476680350025581, 362476761650392563⟩, ⟨625972705606568148, 630027927024244586⟩, true⟩

def words05 : List Nat := [371285292361048992, 371285292303598583, 371285292245152515, 371285292239990124, 371285292169053556, 371285292155069330, 371285292140224494, 371285292088416076, 371285291791565098, 371285291679190617]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469706502442071, 362469787825406137⟩, ⟨1141102960445459581, 1145159851001448035⟩, true⟩

def words06 : List Nat := [371285291617612868, 371285291620151666, 371285291430054803, 371285291230874472, 371285291030672959, 371285290808819970, 371285290516800746, 371285290408825847, 371285290300018592, 371285290192415769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485443312169006, 362485524658161299⟩, ⟨(-21480054031557721), (-17421462269078419)⟩, true⟩

def words07 : List Nat := [371285289984311097, 371285289834138418, 371285289683234245, 371285289685774605, 371285289474402503, 371285289242414487, 371285289009399140, 371285288960491957, 371285288847728338, 371285288853796590]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474600154965547, 362474681523863920⟩, ⟨779657974654182079, 783718258836016387⟩, true⟩

def words08 : List Nat := [371285288857735786, 371285288860284194, 371285288751106226, 371285288790141164, 371285288835884823, 371285288838424802, 371285288640218125, 371285288405871217, 371285288170461618, 371285288077644351]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468099837410894, 362468181229191372⟩, ⟨1260044745276408332, 1264106720333203062⟩, true⟩

def words09 : List Nat := [371285287935827420, 371285287930440109, 371285287924153663, 371285287918976819, 371285287669056671, 371285287476358478, 371285287282325648, 371285287271993906, 371285287096807444, 371285286868167465]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738

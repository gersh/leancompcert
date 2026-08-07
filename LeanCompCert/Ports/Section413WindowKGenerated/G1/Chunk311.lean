import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk311

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362518209436272983, 362518222878933245⟩, ⟨(-1021617311838322279), (-1021334729320824135)⟩, true⟩

def state01 : KState := ⟨⟨362478806929086144, 362478820380789719⟩, ⟨203876798182736012, 204159661991600524⟩, true⟩

def words00 : List Nat := [371285384431739430, 371285384432739581, 371285384134979463, 371285384372152886, 371285384925836174, 371285384926836504, 371285384241699202, 371285383562122406, 371285382888871267, 371285382890014779]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362434879981494311, 362434893442202143⟩, ⟨1570862549852468671, 1571145693830575691⟩, true⟩

def words01 : List Nat := [371285383322763622, 371285383966824337, 371285384599171035, 371285384600172108, 371285384052052417, 371285383531957518, 371285383066877213, 371285383067878064, 371285381750260038, 371285380129021892]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472161223853215, 362472174693535631⟩, ⟨410659767212496174, 410943190524877692⟩, true⟩

def words02 : List Nat := [371285378507430713, 371285377915267978, 371285377357496152, 371285377593757604, 371285377686965751, 371285377687966932, 371285376560759134, 371285376086230532, 371285375611218291, 371285375566986479]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476045969312109, 362476059448107025⟩, ⟨289756007377341650, 290039714408239106⟩, true⟩

def words03 : List Nat := [371285375143700293, 371285374727690642, 371285374796115905, 371285374797218843, 371285374922563501, 371285375081627366, 371285375127555719, 371285375128557260, 371285373802319484, 371285373504446404]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459768219943228, 362459781707671184⟩, ⟨796657437787872731, 796941423039801383⟩, true⟩

def words04 : List Nat := [371285373206039374, 371285373177555329, 371285372045869694, 371285370700749157, 371285369355320612, 371285368326632026, 371285366902512530, 371285366506201685, 371285366109589848, 371285365701990279]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362512063799191764, 362512077295980984⟩, ⟨(-832563111761109351), (-832278844206212847)⟩, true⟩

def words05 : List Nat := [371285365087260778, 371285365294346947, 371285366527931836, 371285366583364721, 371285366584141027, 371285366499384660, 371285366757929163, 371285366759044218, 371285367447469075, 371285368305762243]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464418345015561, 362464431850845518⟩, ⟨652174845224343970, 652459394534804066⟩, true⟩

def words06 : List Nat := [371285369088324304, 371285369089326609, 371285368501629212, 371285368452395987, 371285368471880598, 371285368472883006, 371285367173071195, 371285365863032921, 371285364552658037, 371285364138126070]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470822128942005, 362470835643804839⟩, ⟨452559207718262804, 452844038630209990⟩, true⟩

def words07 : List Nat := [371285363467287977, 371285363099350549, 371285362731108248, 371285362368187844, 371285361423757551, 371285360625770470, 371285360053480239, 371285360054503152, 371285359650470153, 371285359185775019]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503909556341961, 362503923080174224⟩, ⟨(-579161601111694287), (-578876490486775229)⟩, true⟩

def words08 : List Nat := [371285359280022884, 371285359324380163, 371285360393378928, 371285361462729043, 371285362151559806, 371285362152563743, 371285361919361478, 371285362146007263, 371285363396850329, 371285363992921915]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499542321045716, 362499555854048689⟩, ⟨(-442844431352343625), (-442559034648031467)⟩, true⟩

def words09 : List Nat := [371285364490578837, 371285364988569025, 371285366510701106, 371285367526432724, 371285368611280951, 371285369696439408, 371285370785759444, 371285370812999231, 371285371268341121, 371285371724224388]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk311

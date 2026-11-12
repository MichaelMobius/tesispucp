# Lema 3.13 y cobertura logarítmica

Se cotejaron las páginas impresas 82–83 del PDF normativo del [inventario](INVENTARIO_FORMAL_CAPITULO_III.md) con SHA-256 `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`. La base Lean es la PR #20 en `2a99bf9e4672b679cdf09167c54f787315564ddc`.

| Paso | Declaración Lean | Hipótesis y conclusión |
|---|---|---|
| (3.57) | `escalaAuxiliarLog`, `radioCoberturaLog`, `escalaAuxiliarLog_masa` | La escala es `(κ log(m)/(c m))^(1/s)` y el radio es `D η_m`, con `D,c,s>0`. Para `m≥3` y `κ>0` se obtiene `c η_m^s = κ log(m)/m`. |
| Umbrales | `radioLog_eventualmente_admisible` | Si los tamaños tienden a infinito, eventualmente `m≥3`, `0<η_m≤η₀`, `κ log(m)≤m` y `0<ρ_m≤r₀`. Los límites de escala y radio provienen de `log(m)/m→0`. Los umbrales `η₀,r₀` son positivos y pueden coincidir al usar la Hipótesis 3.2. |
| Número de celdas | `cardinal_particion_log` | La masa mínima es positiva para `m≥3`. La disjunción y la masa total a lo sumo uno dan `#celdas ≤ m/(κ log(m))`. |
| (3.58) | `falloOcupacion_le_escala_log` | La cota exponencial con esa masa mínima y el cardinal anterior da `m^(1−κ)/(κ log(m))`. El evento es el complemento de `todasCeldasOcupadas`. |
| Serie de fallos | `sumable_mayoranteFalloLog_de_tamanos` | Cuando `m(n)≥n` eventualmente y `κ>2`, el mayorante evaluado en `m(n)` se acota eventualmente por `n^(1−κ)/κ`. Se usa `log(m(n))≥1` eventual y que la potencia de exponente `1−κ<0` decrece. `Real.summable_nat_rpow` da la p-serie de exponente `κ−1>1`. |
| Lema 3.13 | `lema313_cobertura_logaritmica` | Para cada tamaño admisible obtiene un evento medible de fallo con la cota (3.58) y cobertura en su complemento. Demuestra la cobertura eventual casi segura para los prefijos de tamaños `m(n)` en el espacio probabilístico común. |

## Alcance y mensurabilidad

El teorema usa un espacio pseudométrico y un factor de diámetro arbitrario `D>0`. El caso euclidiano del PDF se obtiene por especialización. `ParticionesMinimas.particionesOcupacionLog` reutiliza las particiones de la interfaz 2D con `D=√2`. Se admite cualquier dimensión de masa positiva. La sucesión original del lema es la instancia `m(n)=n`. Los índices `Fin m` enumeran las primeras `m` muestras de una única familia i.i.d.

Para cada tamaño admisible se elige una partición a la escala auxiliar. Su ocupación se expresa mediante intersecciones y uniones finitas de preimágenes medibles. Borel–Cantelli se aplica a esos fallos, cuya serie en `ENNReal` se deduce de la serie real mediante `tsum_fallos_ne_top_de_mayorante`. La ocupación implica la cobertura geométrica por la cota de diámetro, de modo que la prueba usa la mensurabilidad del evento finito. El umbral del radio final garantiza su validez para las cotas de masa de bolas al aplicar la cobertura después. La estimación de ocupación por sí sola utiliza las masas inferiores de las celdas.

Se eligen las particiones de una cola determinista para que cada tamaño desplazado sea admisible. La cobertura se devuelve a los índices originales porque trasladar un índice natural por una constante preserva `atTop`. La independencia se usa entre muestras de una misma familia en la cota de ocupación. El primer lema de Borel–Cantelli prescinde de independencia entre tamaños. Para dos familias se intersectan las conclusiones de probabilidad uno y las propiedades eventuales mediante `Filter.Eventually.and`. Para un par fijo de tamaños, la probabilidad de fallo de esa intersección se controla por subaditividad de los dos complementos.

## Integraciones pendientes

- **Proposición 3.14.** Aplicar L3.13 a `s=d` y `s=d−1`, combinar los eventos finitos y usar `objetivoCoberturaIntegral_de_hipotesis` con los dos radios en 2D. `pesoCobertura`, `pesoRegularizacionIgual` y `factor_mul_peso_igual` permiten relacionar esos radios con los nuevos pesos. Queda verificar (3.60)–(3.63), incluida la tasa como suma de dos términos en sus tamaños respectivos y las hipótesis de minimalidad para el objetivo logarítmico. La extensión a dimensión ambiente arbitraria requiere generalizar la cota poblacional que usa las dimensiones de masa 2 y 1.
- **Proposición 3.15.** Una sola instancia de L3.13 con `s=2`, `D=√2`, `c=1/9` y `κ=3` aporta la parte probabilística. Quedan la ley uniforme del cuadrado, la verificación del umbral numérico `m≥310`, las identidades de (3.64), el funcional interior con traza exacta y la transferencia de la tolerancia a la tasa poblacional de (3.66).

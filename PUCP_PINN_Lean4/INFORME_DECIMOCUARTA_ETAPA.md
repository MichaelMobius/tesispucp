# Auditoría del Teorema 3.8 en dimensión dos

El enunciado se cotejó con las páginas impresas 66–67 de la tesis, las Hipótesis 3.2 y 3.7 (páginas 43–44 y 64–65) y la elección de pesos (3.23). `teorema38_dim2` reúne las tres conclusiones para una misma realización, en notación `∀ᵐ ω ∂P` y a lo largo de la misma sucesión de pares de tamaños. La pérdida tiene tasa `mr(n)^(-α/2)`, los dos supremos puntuales tienden a cero y sus tasas son `mr(n)^(-α²/[2(2α+2)])` y `mr(n)^(-α²/[2(2α+1)])`, respectivamente.

## Cadena de dependencias

| Tramo | Qué se asume y qué se deriva |
|---|---|
| Hipótesis 3.2 y ocupación | `DatosMasa38` fija los soportes medibles acotados, concentración, cotas superiores de bola y particiones medibles a cada escala pequeña. `Muestreo38` fija leyes, mensurabilidad e independencia interna de cada sucesión. Los radios finales tienden a cero. Se escoge una cola común donde son admisibles y se especializan las particiones a las escalas auxiliares correspondientes. |
| (3.13) y (3.26) | La cota integral de `CoberturaIntegral` y la ocupación de `OcupacionAleatoria` intervienen a través de `tasa_poblacional_eventual_casi_segura`. La tasa vuelve al índice original mediante `map_add_atTop_eq_nat`. La cota eventual de pérdida se proyecta de ese resultado para suministrar `h26`. |
| Problema y regularización | `Operadores38` fija operadores, datos y seminormas. Su método `base` produce el registro `ProblemaPINN` y fija ambos pesos de regularización en el valor de (3.23), que es positivo. La familia aleatoria se obtiene con `problemaMuestral`, que reemplaza los campos de muestra por los prefijos de las sucesiones i.i.d. |
| Hipótesis 3.7 | Las selecciones son funciones hacia `Hm n` con coerciones medibles. En casi toda realización se exige minimalidad global, interpolación exacta y una cota finita común de la regularidad del comparador para todos los índices. La continuidad espacial se deriva de `CotasHolder`. La acotación, concentración y continuidad dan integrabilidad. Los controles Hölder uniformes de los minimizadores se deducen mediante comparación. |
| (3.27) y (3.28) | `convergencia_y_tasas_uniformes_ae` deduce masa local de las mismas particiones a todas las escalas y aplica la transferencia de integral cuadrática a norma supremo. Usa dimensiones de masa 2 y 1 y conserva `mr(n)` en las dos tasas. |

## Alcance frente al enunciado literal

- Se formalizan las tres conclusiones asintóticas escalares para `d=2`. El dominio y la frontera se abstraen como espacios pseudométricos con los exponentes y diámetros de la tesis. La regularidad geométrica del dominio, la inclusión de la frontera muestreada en la frontera topológica y las densidades no se codifican como premisas separadas. Para este argumento basta suministrar los datos de masa y concentración que la tesis postula. La independencia entre los dos muestreos no se usa, pues se intersectan dos eventos casi seguros.
- Los candidatos y operadores son abstractos. La condición `Hm ⊆ C^{k,α}` y la arquitectura neuronal se reflejan solo en las cotas que necesita la prueba para `L[h]` y `B[h]`. `CotasHolder` admite constantes que dominan los seminormas. Para identificar el funcional literalmente con el de la tesis se toman los seminormas exactos. Las selecciones, la interpolación y la existencia de minimizadores globales permanecen como premisas.
- Las selecciones se tipan globalmente en sus clases y las propiedades de optimización se exigen casi seguramente. Las clases se indexan por `n`. Una familia que depende solo del par `(mr(n), mb(n))` es una instancia. El crecimiento y la relación `mr(n) ≤ K mb(n)^2` son eventuales. Los tamaños son positivos desde el primer índice para que cada registro de pérdida empírica esté definido. La prueba descarta un prefijo finito para especializar particiones.
- El texto da (3.26) sobre el evento de cobertura. La versión integrada afirma la tasa casi segura a lo largo de la sucesión, tras la cobertura eventual. La cota determinista condicionada a cobertura sigue disponible en `CoberturaIntegral.lean`.

## Mensurabilidad

`measurable_perdida_problemaMuestral` aplica el criterio de la PR #15 a la familia integrada índice por índice. Requiere mensurabilidad conjunta de `(h,x) ↦ L[h](x)` y `(h,y) ↦ B[h](y)`, además de datos y selección medibles. Son condiciones suficientes para la integral paramétrica y no se deducen de la continuidad espacial para cada candidato. La condición conjunta se comprueba por separado al instanciar una clase concreta.

`measurable_supResiduo_de_denso` identifica el supremo de un residuo continuo y acotado con el supremo en una sucesión densa del soporte. Exige mensurabilidad de las evaluaciones en esa sucesión. La mensurabilidad conjunta de los operadores y la de la selección son suficientes para obtener dichas evaluaciones. `prob_uno_convergencia_sup` convierte la convergencia casi segura de los dos supremos medibles en una igualdad de probabilidad uno para el conjunto exacto de convergencia. El teorema integrado usa `∀ᵐ` y no exige estas condiciones de mensurabilidad adicional.

## Verificación

El módulo se importa desde `TesisPINN.lean`. Sus directivas `#print axioms` se ejecutan con `lake build` y se registran en el [CI de la PR #16](https://github.com/MichaelMobius/tesispucp/pull/16/checks). Las dependencias fijadas son Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.

# Etapa 23 · Estabilidad elíptica y convergencia uniforme

Se cotejaron las páginas impresas 6–7 y 91–98 del PDF normativo identificado en el [inventario](INVENTARIO_FORMAL_CAPITULO_III.md). La base es la PR #24, commit `976fd52bd620695cbb5dfe03a98f105b9e228779`.

## Correspondencia

| Resultado | Declaración Lean | Alcance |
|---|---|---|
| (1.1)–(1.2), expansión del operador | `OperadorDivergencia.aplica_eq_noDivergente`, `OperadorEliptico.aplica_eq_suma` | Regla del producto en cada coordenada y suma finita. Se obtienen $\widetilde b^j=\sum_iD_i a^{ij}+b^j+c^j$ y $\widetilde c=\sum_iD_i b^i+d$. |
| Hipótesis 3.16, parte usada por la estabilidad | `OperadorEliptico.Datos`, `OperadorEliptico.ContinuoEn`, `OperadorDivergencia.continuo_noDivergente`, `OperadorDivergencia.cotas_noDivergente` | Matriz simétrica, elipticidad de forma cuadrática con $\lambda_0>0$, cota de transporte y $\widetilde c\le0$. Se deduce la continuidad expandida de la regularidad $C^1$ de los coeficientes principales y $b^i$ y la continuidad de los restantes. |
| Máximo débil clásico | `OperadorEliptico.maximo_debil` | Adaptación de `EllipticPdes.Classical.weak_maximum_principle_of_nonneg` en cualquier dimensión positiva. |
| Barrera de L3.17 | `derivada_barreraExponencial`, `segunda_derivada_barreraExponencial`, `aplica_barreraExponencial`, `barrera317` | Barrera exponencial, derivadas de primer y segundo orden, y normalización para obtener $\mathcal L\psi\le-1$ en $U$. |
| (3.67) | `lema317_estabilidad_uniforme`, `lema317_estabilidad_Linfty` | Cota en $\overline U$ por el supremo de frontera y el residuo interior, en dimensión arbitraria positiva. La versión $L^\infty$ usa Lebesgue restringida a $U$. |
| (3.68) | `cota318_error_dirichlet_Linfty` | Se aplica la cota a $h-u^*$, con residuo $\mathcal Lh-f$ y error de frontera $h-g$. |
| (3.69)–(3.70) | `teorema318_dim2` | Convergencia y tasa casi seguras en 2D a partir de `teorema38_dim2`, para una solución clásica dada. |
| (3.71) | `energia_sobolev_plano_volumen`, `energia_cuadrado_uniforme` | Corresponde al Lema 3.19 de energía de Poisson, en la página 98. Su alcance se registra por separado. |

## Signos, constantes y normas

La parte principal de la tesis tiene signo positivo. El operador de EllipticPDE que se usa para el máximo es $-\mathcal L$, con parte principal negativa y coeficiente de orden cero $-\widetilde c\ge0$. Sus subsoluciones satisfacen $-\mathcal Lw\le0$. La cota de $|\widetilde b^i|$ sirve para ambos signos del transporte. El argumento usa un abierto no vacío y acotado, funciones $C^2$ en el abierto y continuidad en su clausura.

Se toma $e=e_1$, $|\langle e,x\rangle|\le r$ en la clausura, $R=r+1$ y $\gamma=2+2B/\lambda_0$. Para $q=1-\exp(\gamma(\langle e,x\rangle-R))$ las derivadas tienen factores $-\gamma\exp(\cdots)$ y $-\gamma^2\exp(\cdots)$ en la dirección $e$, y se anulan en direcciones ortogonales según las fórmulas bilineales. La elipticidad y la cota de $\widetilde b^1$ dan $\mathcal Lq\le-\delta$, con $\delta=\exp(\gamma(-r-R))(\lambda_0\gamma^2-B\gamma)>0$. El término $\widetilde c q$ es no positivo. Se usa $\psi=q/\delta$ y $C_0=1/\delta$, elegido antes de $v$. Los dos signos se controlan aplicando el máximo a $\pm v-M-F\psi$.

`supResiduo_closure` identifica el supremo absoluto sobre $U$ con el de la clausura para una función continua y acotada allí. `supResiduo_eq_Linfty` identifica el supremo puntual sobre un abierto con el esencial para una función continua y acotada y una medida positiva en abiertos no vacíos. La prueba de T3.18 usa el residuo en $U$, tal como en (3.68). Si se dispone de una extensión continua a la clausura, el lema sobre la clausura justifica usar allí el mismo supremo.

## Transferencia y existencia

`operadores318` aplica el operador elíptico al candidato y lo evalúa en la frontera geométrica, con las seminormas Hölder exactas del operador y de la restricción. `soporte_de_DatosMasa38` deduce $\operatorname{supp}\mu_b=\partial U$ de la concentración y de la masa mínima a todas las escalas. Se usa la misma clase, los mismos pesos y los mismos prefijos que en T3.8. La solución exacta satisface $\mathcal L u^*=f$ en el abierto y $u^*=g$ en la frontera.

La tasa de frontera tiene exponente $p_b=\alpha^2/[2(2\alpha+1)]$ y la interior $p_r=\alpha^2/[2(2\alpha+2)]$. Como $p_r\le p_b$ y $m_r\ge1$, la cota combinada tiene tasa $m_r^{-p_r}$. La comparación de exponentes se prueba también para $d\ge2$. La conclusión probabilística integrada queda en 2D porque la declaración disponible del Teorema 3.8 trabaja con dimensiones de masa 2 y 1. Se conservan como premisas la selección mensurable, la comparación exacta y la regularidad de los candidatos, entre las demás hipótesis de T3.8.

La existencia clásica usada en la tesis procede del Teorema 6.13 de Gilbarg–Trudinger. Este teorema usa coeficientes y fuente acotados y localmente Hölder, el signo del término de orden cero, elipticidad y esfera exterior en cada punto de frontera, con dato de borde continuo. Produce una solución continua hasta la frontera y de regularidad clásica en el interior. La revisión fijada de EllipticPDE aporta máximo y unicidad clásicos y resultados variacionales. La existencia clásica general con esfera exterior queda pendiente de formalización. Ninguna condición de esfera exterior interviene en el lema de estabilidad. [Gilbarg–Trudinger, capítulo 6](https://link.springer.com/book/10.1007/978-3-642-61798-0)

## Siguiente etapa

Priorizar la Proposición 3.21. Su barrera cuadrática para Poisson puede reutilizar `OperadorEliptico.maximo_debil`, las identidades de linealidad y los lemas de supremos. La barrera exponencial da estabilidad con una constante general. La cuadrática requiere demostrar su propia acción y el máximo exacto para obtener la constante de P3.21. P3.22 y C3.23 siguen la ruta de la base seno y el control de la serie. Las construcciones de Taylor y Hermite siguen siendo dependencias separadas de los comparadores para las clases neuronales concretas.

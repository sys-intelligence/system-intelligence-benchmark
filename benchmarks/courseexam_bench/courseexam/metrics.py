from inspect_ai.scorer import Metric, SampleScore, metric


@metric
def points_accuracy() -> Metric:
    def metric_fn(scores: list[SampleScore]) -> float:
        total_earned = 0.0
        total_possible = 0.0

        for sample_score in scores:
            metadata = sample_score.score.metadata or {}
            total_earned += metadata.get("points_earned", 0)
            total_possible += metadata.get("points_possible", 0)

        if total_possible == 0:
            return 0.0

        return total_earned / total_possible

    return metric_fn


@metric
def total_points_earned() -> Metric:
    def metric_fn(scores: list[SampleScore]) -> float:
        total = 0.0

        for sample_score in scores:
            metadata = sample_score.score.metadata or {}
            total += metadata.get("points_earned", 0)

        return total

    return metric_fn


@metric
def total_points_possible() -> Metric:
    def metric_fn(scores: list[SampleScore]) -> float:
        total = 0.0

        for sample_score in scores:
            metadata = sample_score.score.metadata or {}
            total += metadata.get("points_possible", 0)

        return total

    return metric_fn

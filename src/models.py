from enum import StrEnum


class AnthropicModel(StrEnum):
    DEBUG: str = "anthropic/claude-3-haiku-20240307"
    BEST: str = "anthropic/claude-3-5-sonnet-20241022"


class OpenAIModel(StrEnum):
    DEBUG: str = "openai/gpt-4o-mini-2024-07-18"
    BEST: str = "openai/o3-mini-2025-01-31"

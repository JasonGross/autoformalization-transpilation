from enum import StrEnum


class AnthropicModel(StrEnum):
    DEBUG = "anthropic/claude-3-haiku-20240307"
    SONNET35 = "anthropic/claude-3-5-sonnet-20241022"
    BEST = "anthropic/claude-3-7-sonnet-20250219"


class OpenAIModel(StrEnum):
    DEBUG = "openai/gpt-4o-mini-2024-07-18"
    O1MINI = "openai/o1-mini-2024-09-12"
    O1PREVIEW = "openai/o1-preview-2024-09-12"
    BEST = "openai/o3-mini-2025-01-31"
    O1 = "openai/o1-2024-12-17"

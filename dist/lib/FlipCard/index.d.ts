import React from 'react';
import { StyledSystemProps } from '../GenericComponent';
interface FlipCardProps extends StyledSystemProps {
    image: string;
    listItems: string[];
    headingText: string;
    value: string;
    startColor?: string;
    endColor?: string;
}
declare const FlipCard: React.FC<FlipCardProps>;
export default FlipCard;
